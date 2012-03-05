{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Tiger where

import Control.Monad.State
import Data.Dynamic
import Data.List
import Data.Maybe
import Debug.Trace
import Data.IORef
import System.IO.Unsafe

import Expressions(Expr(Const, Apply, Var, IfExpr, LetExpr, Lambda, HashMap), exsym, upsert)
import Stats(Path(PathAll, PathCons, PathNil), pappend, pinit, plast)
import Language(parseExpr, parseFile)

mkCell :: Op -> Op
mkCell = Cell . unsafePerformIO . newIORef

readCell :: Op -> Op
readCell (Cell r) = unsafePerformIO (readIORef r)

writeCell :: Op -> Op -> Op
writeCell (Cell r) op = unsafePerformIO (writeIORef r op >> return op)

mapCell' :: Op -> (Op -> Op) -> Op
mapCell' (Cell r) f = unsafePerformIO $ do
  op <- readIORef r
  let op' = f op
  writeIORef r op'
  return op'

mapCell :: Op -> (Op -> Op) -> Op
mapCell c@(Cell r) f = unsafePerformIO $ do
  op <- readIORef r
  let op' = f op
  writeIORef r op'
  case op' of
    (Val _) -> return op'
    (Bin _ _) -> return op'
    (Clr _ _) -> return op'
    _ -> return c

data Op =
  App Op Op -- function application
  | Val Dynamic -- a constant packed in Dynamic
  | Ref Int -- reference to a slot
  | Lam [Int] Op -- lambda definition, declares external symbols as slots
  | Clr [Op] Op -- a closure of a lambda
  | Cap [Op] Op -- a closure of an expression
  | Bin String (Env -> Op -> Op) -- builtin function
  | Cell (IORef Op) -- wraps an expression to allow results of lazy evaluation
  | Hash [(String, Op)] -- a map data structure
  | Let [Op] Op -- recursive let binding

instance Show Op where
  show (App a b) = "(App " ++ show a ++ " " ++ show b ++ ")"
  show (Val d) = "(Val " ++ showDynamic d ++ ")"
  show (Lam exts x) = "(Lam " ++ show exts ++ " " ++ show x ++ ")"
  show (Ref i) = "(Ref " ++ show i ++ ")"
  show (Clr exts x) = "(Clr " ++ show exts ++ " " ++ show x ++ ")"
  show (Cap exts x) = "(Cap " ++ show exts ++ " " ++ show x ++ ")"
  show (Bin s _) = "(Bin " ++ s ++ ")"
  show c@(Cell _) = "(Cell ?)"
  show (Hash kvs) = "(Hash " ++ show kvs ++ ")"
  show (Let bs x) = "(Let " ++ show bs ++ show x ++ ")"

showDynamic :: Dynamic -> String
showDynamic d | dynTypeRep d == typeOf (error "" :: String) = (fromDyn d "?")
showDynamic d | dynTypeRep d == typeOf (error "" :: Int) = show (fromDyn d 0 :: Int)
showDynamic d | dynTypeRep d == typeOf (error "" :: Integer) = show (fromDyn d 0 :: Integer)
showDynamic d | dynTypeRep d == typeOf (error "" :: Bool) = show (fromDyn d True)
showDynamic _ = "?"

stringType = typeOf (error "" :: String)
intType = typeOf (error "" :: Int)
boolType = typeOf (error "" :: Bool)

printRef :: Env -> Int -> String
printRef env i | i > 0 = printOp env $ mem env i
printRef _ i = show i

printOp :: Env -> Op -> String
printOp env (App a b) = "(App " ++ printOp env a ++ " " ++ printOp env b ++ ")"
printOp env (Lam exts x) = "(Lam " ++ show exts ++ " " ++ printOp env x ++ ")"
printOp env (Ref i) = "(Ref " ++ printRef env i ++ ")"
printOp env (Clr exts x) = "(Clr [" ++ intercalate ", " (map (printOp env) exts) ++ "] " ++ printOp env x ++ ")"
printOp env (Cap exts x) = "(Cap [" ++ intercalate ", " (map (printOp env) exts) ++ "] " ++ printOp env x ++ ")"
printOp env c@(Cell _) = "(Cell" ++ printOp env (readCell c) ++ ")"
printOp env (Hash kvs) ="(Hash " ++ show (map (\(k, v) -> (k, printOp env v)) kvs) ++ ")"
printOp env (Let bs x) = "(Let " ++ show (map (printOp env) bs) ++ printOp env x ++ ")"
printOp _ op = show op

data Env = Env {global :: [Op], local :: [Op]}

mem :: Env -> Int -> Op
mem env i | i > 0 = global env !! (i - 1)
mem env i = local env !! (0 - i)

reduce :: Env -> Op -> Op
reduce env (App f x) = case reduce env f of
  (Bin _ b) -> reduce env (b env (toCell $ toCapture env x))
  c@(Clr bs y) -> reduce (env {local = c:(toCell $ toCapture env x):bs}) y
reduce env v@(Val _) = v
reduce env (Ref i) = reduce env (mem env i)
reduce env (Lam xs y) = Clr (map (mem env) xs) y
reduce env c@(Clr _ _) = c
reduce env (Cap ls x) = reduce (env {local = ls}) x
reduce env b@(Bin _ _) = b
reduce env c@(Cell _) = mapCell' c (reduce env)
reduce env (Hash h) = Hash (map (\(k, v) -> (k, toCell (toCapture env v))) h)
reduce env (Let bs x) = reduce (env {local = (local env) ++ bs'}) x
  where
    bs' = map (toCellCapture (env {local = (local env) ++ celled})) celled
    celled = map toCell bs

force :: Env -> Op -> Op
force env e = force' env (reduce env e)
  where
    force' env (Hash h) = Hash $ map (\(k, v) -> (k, force env v)) h
    force' _ x = x

toCell :: Op -> Op
toCell c@(Cell _) = c
toCell v@(Val _) = v
toCell c@(Clr _ _) = c
toCell b@(Bin _ _) = b
toCell x = mkCell x

toCellCapture :: Env -> Op -> Op
toCellCapture env c@(Cell _) = mapCell c (toCapture env)
toCellCapture _ x = x

toCapture :: Env -> Op -> Op
toCapture env (Ref i) = toCapture env (mem env i)
toCapture env c@(Cell _) = c
toCapture env v@(Val _) = v
toCapture env c@(Clr _ _) = c
toCapture env b@(Bin _ _) = b
toCapture env c@(Cap _ _) = c
toCapture env x = Cap (local env) x

asVal :: (Typeable a) => Op -> a
asVal (Val d) = fromDyn d (error $ "dynCast " ++ show d)
asVal op = error $ show op ++ " is not a Val!"

val :: (Typeable a) => a -> Op
val = Val . toDyn

add_ = Bin "x+" (\_ x -> Bin "+y" (\env y -> val $ (asVal (reduce env x) :: Int) + (asVal (reduce env y) :: Int)))
lessThan_ = Bin "x<" (\_ x -> Bin "<y" (\env y -> val $ (asVal (reduce env x) :: Int) < (asVal (reduce env y) :: Int)))
get_ = Bin "get" (\env k -> Bin "get2" (\_ h -> get env (reduce env k) (reduce env h)))
  where
    get env (Val k) (Hash kvs) | dynTypeRep k == stringType = let k' = (fromDyn k (error "") :: String) in
      fromMaybe (error $ "could not find " ++ show k' ++ " in " ++ show kvs) $ lookup k' kvs
    get env (Val k) (Hash kvs) | dynTypeRep k == intType = fromJust $ lookup (show (fromDyn k (error "") :: Int)) kvs
    get _ k h = error ("k is " ++ show k ++ ", h is " ++ show h)

set_ = Bin "set" (\env k -> Bin "set2" (\_ v -> Bin "set3" (\env2 h -> set (reduce env k) v (reduce env h))))
  where
    set (Val k) v (Hash h) | dynTypeRep k == stringType = Hash $ upsert (fromDyn k (error "")) v (const v) h
    set (Val k) v (Hash h) | dynTypeRep k == intType = Hash $ upsert (show (fromDyn k (error "") :: Int)) v (const v) h

keys_ = Bin "keys" (\env h -> keys (reduce env h))
  where
    keys (Hash h) = Hash $ zip (map show [0..]) (map (Val . toDyn . fst) h)

merge_ = Bin "merge" (\env a -> Bin "merge2" (\env2 b -> merge (reduce env a) (reduce env2 b)))
  where
    merge (Hash a) (Hash b) = Hash $ a ++ b

size_ = Bin "size" (\env h -> size (reduce env h))
  where
    size (Hash h) = Val $ toDyn $ (length h :: Int)
    size x = error $ "expected a Hash but got " ++ show x
    
if_ = Bin "if" (\envC c -> Bin "if2" (\envT t -> Bin "if3" (\envE e -> if (asVal (reduce envC c)) then t else e)))

stdEnv = Env {global = [add_, lessThan_, get_, set_, keys_, size_, if_], local = []}

testAdd n = [Lam [1] $ Ref (n+1), Lam [-1, -2] $ Ref (n+2), App (Ref 3) (Ref (-1))]
testLet = Let [val (5 :: Int)] (App (App (Ref 1) (val (8 :: Int))) (Ref (0 - length test)))
testLetRec = Let [val (5 :: Int), (App (App (Ref 1) (val (9 :: Int))) (Ref (0 - length test)))] (Ref (0 - length test - 1))

test = [val (1 :: Int), val (2 :: Int), val (5 :: Int), val (100000 :: Int), val "+", val "2", Hash [("+", Ref 1), ("2", Ref (-1))], App (Ref 3) (Ref (-5)), App (Ref (-7)) (Ref (-6))]

testEnv = stdEnv {local = test}

data TransContext = TransContext {localId :: Int, path :: Path, mapping :: [(Path, Int)]}

pathToRef :: TransContext -> Path -> Op
pathToRef ctx p = fromMaybe (throughHashes ctx (pinit p) [plast p]) (fmap Ref $ lookup p $ mapping ctx )

throughHashes :: TransContext -> Path -> [String] -> Op
throughHashes ctx PathNil ks = error $ "not found " ++ show ks ++ " in " ++ show (mapping ctx)
throughHashes ctx p ks = case lookup p (mapping ctx) of
  (Just i) -> mkHashChain (pathToRef ctx (tp' "get")) (Ref i) (reverse ks)
  Nothing -> throughHashes ctx (pinit p) (plast p : ks)

mkHashChain :: Op -> Op -> [String] -> Op
mkHashChain _ h [] = h
mkHashChain get h (k:ks) = mkHashChain get (App (App get (val k)) h) ks

addPathToLocalRef :: TransContext -> Path -> TransContext
addPathToLocalRef ctx p = ctx {mapping = upsert p (-id) (const (-id)) (mapping ctx), localId = id + 1}
  where id = localId ctx

exprToOp :: TransContext -> Expr -> Op
exprToOp _ (Const d) = Val d
exprToOp ctx (Var p) = pathToRef ctx p
exprToOp ctx (IfExpr c t e) = exprToOp ctx (Apply (Apply (Apply (Var (tp' "if")) c) t) e)
exprToOp ctx (Apply f x) = App (exprToOp ctx f) (exprToOp ctx x)
exprToOp ctx (LetExpr p x y) = Let [exprToOp ctx' x] (exprToOp ctx' y)
  where ctx' = addPathToLocalRef ctx p
exprToOp ctx l@(Lambda p x) = Let exts $ Lam bexts (exprToOp ctx' x)
  where
    ctx' = foldl addPathToLocalRef (ctx {localId = 1}) (p : exsym l)
    exts = map (pathToRef ctx) (exsym l)
    n = localId ctx
    bexts = map (\i -> (-i)) $ take (length $ exsym l) $ [n..]
exprToOp ctx (HashMap m) = Let vals (Hash h)
  where
    keys = map fst m
    n = localId ctx
    h = zip keys $ map (\i -> Ref (-i)) [n..]
    n' = n + length keys
    ctx' = foldl addPathToLocalRef ctx $ map tp' keys
    vals = map (\(k, v) -> exprToOp ctx' v) m

tp = foldr PathCons PathNil
tp' k = tp [k]

var = Var . tp'

iconst :: Int -> Expr
iconst = Const . toDyn

testConv = Lambda (tp' "n") (LetExpr (tp' "f") (Lambda (tp' "i") (IfExpr (Apply (Apply (var "<") (var "i")) (var "n")) (Apply (var "f") (Apply (Apply (var "+") (var "i")) (Const $ toDyn (1 :: Int)))) (var "i"))) (Apply (var "f") (Const $ toDyn (1 :: Int))))
testHash = LetExpr (tp' "a") (HashMap [("b", HashMap [("c", Const $ toDyn (13 :: Int))])]) (Var $ tp ["a", "b"])
testHashRec = LetExpr (tp' "h") (HashMap [("a", HashMap [("0", iconst 1), ("1", iconst 0)]), ("b", Var $ tp ["a", "1"])]) (Apply (Apply (var "get") (Const $ toDyn "b")) (var "h") )

testCtx = TransContext {localId = 0, path = PathNil, mapping = [(tp' "+", 1), (tp' "<", 2), (tp' "get", 3), (tp' "set", 4), (tp' "keys", 5), (tp' "size", 6), (tp' "if", 7)]}

setAll :: (Ord k) => [(k, v)] -> [(k, v)] -> [(k, v)]
setAll a b = foldl (\h (k, v) -> upsert k v (const v) h) a b

propagate :: [(Int, Op)] -> Int -> Op -> Op
propagate rs n (Let bs x) = if null bs' then x' else l'
  where
    (bs', deleted) = processLetBs x n bs
    indexChanges = computeIndexChanges (map fst deleted) (length bs)
    deletedRs = map (\(i, x) -> (adjust i, x)) deleted
    renamedRs = map (\(old, new) -> (adjust old, Ref $ adjust new)) indexChanges
    adjust i = -n - i
    rs' = rs `updateRs` deletedRs `updateRs` renamedRs
    n' = n + length bs'
    x' = propagate rs' n' x
    l' = Let (map (propagate rs' n') bs') x'
propagate rs n (Lam xs y) = Lam xs' (propagate rs' (2 + length xs') y)
  where
    (xs', deleted) = processLamXs rs xs
    indexChanges = computeIndexChanges (map fst deleted) (length xs)
    deletedRs = map (\(i, x) -> (adjust i, x)) deleted
    renamedRs = map (\(old, new) -> (adjust old, Ref $ adjust new)) indexChanges
    rs' = deletedRs ++ renamedRs
    adjust i = -2 - i
propagate rs n (App f x) = App (propagate rs n f) (propagate rs n x)
propagate rs n (Hash h) = Hash $ map (\(k, v) -> (k, propagate rs n v)) h
propagate rs n (Ref i) = case lookup i rs of
  Nothing -> Ref i
  (Just x) -> x
propagate _ _ x = x

computeIndexChanges :: [Int] -> Int -> [(Int, Int)]
computeIndexChanges cs n = f cs 0 0
  where
    f [] off i = if (i == n || off == 0) then [] else (i, i - off) : f [] off (i+1)
    f (c:cs) off i | c > i = (i, i - off) : f (c:cs) off (i+1)
    f (c:cs) off i | c == i = f cs (off+1) (i+1)

processLamXs :: [(Int, Op)] -> [Int] -> ([Int], [(Int, Op)])
processLamXs rs xs = f xs 0 [] []
  where
    f [] n xs' cs = (reverse xs', reverse cs)
    f (x:xs) n xs' cs = case lookup x rs of
      Nothing -> f xs (n+1) (x:xs') cs
      (Just (Ref i)) -> f xs (n+1) (i:xs') cs
      (Just op) -> f xs (n+1) xs' ((n, op):cs)

processLetBs :: Op -> Int -> [Op] -> ([Op], [(Int, Op)])
processLetBs x n bs = f bs 0 [] []
  where
    f [] _ bs' cs = (reverse bs', reverse cs)
    f (b:bs) n bs' cs = case b of
      v@(Val _) -> f bs (n+1) bs' ((n, v):cs)
      b@(Bin _ _) -> f bs (n+1) bs' ((n, b):cs)
      r@(Ref _) -> f bs (n+1) bs' ((n, r):cs)
--      x | isInlinable n x -> f bs (n+1) bs' ((n, x):cs)
      _ -> f bs (n+1) (b:bs') cs
    isInlinable i b = (countUses i' b == 0) && (1 >= foldl (+) 0 (map (countUses i') (x:bs)))
      where i' = -n - i

updateRs :: [(Int, Op)] -> [(Int, Op)] -> [(Int, Op)]
updateRs a b = foldl (updateR True) a b
  where
    updateR t [] u = if t then [u] else []
    updateR _ ((k, _):rs) u@(k', v') | k==k' = (k, v') : updateR False rs u
    updateR t ((k, Ref i):rs) u@(k', v') | i==k' = (k, v') : updateR t rs u
    updateR t (r:rs) u = r : updateR t rs u

countUses :: Int -> Op -> Int
countUses n (Ref i) | i==n = 1
countUses n (Lam xs _) | elem n xs = 2
countUses n (App f x) = countUses n f + countUses n x
countUses n (Let bs x) = foldl (+) (countUses n x) (map (countUses n) bs)
countUses n (Hash h) = foldl (+) 0 (map (countUses n . snd) h)
countUses _ _ = 0


{-
App Op Op -- function application
  | If Op Op Op -- if then else expressionTiger.hs
  | Val Dynamic -- a constant packed in Dynamic
  | Ref Int -- reference to a slot
  | Lam [Int] Op -- lambda definition, declares external symbols as slots
  | Bin String (Env -> Op -> Op) -- builtin function
  | Hash [(String, Op)] -- a map data structure
  | Let [Op] Op -- recursive let binding
-}
mapOp :: (Monad m) => (Op -> m Op) -> Op -> m Op
mapOp processStage (App f x) = do
  f' <- processStage f
  x' <- processStage x
  return $ App f' x'
mapOp _ v@(Val _) = return v
mapOp _ r@(Ref _) = return r
mapOp processStage (Lam xs y) = do
  y' <- processStage y
  return $ Lam xs y'
mapOp _ b@(Bin _ _) = return b
mapOp processStage (Hash h) = do
  h' <- mapM mapKV h
  return $ Hash h'
  where
    mapKV (k, v) = do
      v' <- processStage v
      return (k, v')
mapOp processStage (Let bs x) = do
  bs' <- mapM processStage bs
  x' <- processStage x
  return $ Let bs' x'


unluckyStage :: Op -> Maybe Op
unluckyStage (Ref i) = Just (Ref 13)
unluckyStage x = mapOp unluckyStage x
