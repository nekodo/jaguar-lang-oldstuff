{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, DeriveDataTypeable, BangPatterns #-}
module Tiger where

import Control.Monad.Identity
import Control.Monad.State
import Data.Dynamic
import Data.Foldable(foldlM)
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Data.IORef
import System.IO.Unsafe

import Expressions(Expr(Const, Apply, Var, IfExpr, LetExpr, Lambda, HashMap, ModList, ListExpr), Module(Module), exsym, upsert)
import Stats(Path(PathAll, PathCons, PathNil), pappend, pinit, plast, Stat(keys, deps), sortForEval)
import Language(parseExpr, parseFile, parseModule)

import TigerAST
import TigerOptimisations

mkCell :: Op -> Op
mkCell !op = Cell . unsafePerformIO . newIORef $ op

indent :: [String] -> [String]
indent = map ("  " ++)

isSmall :: [String] -> Bool
isSmall [] = True
isSmall [s] = length s < 30
isSmall _ = False

parens [s] = ["(" ++ s ++ ")"]
parens (s:ss) = ("(" ++ s) : parensLast ss
  where
    parensLast [s] = [s ++ ")"]
    parensLast (s:ss) = s : parensLast ss

prettyPrint :: Int -> Op -> [String]
prettyPrint n (Val d) = [showDynamic d]
prettyPrint n (Ref i) = ["@" ++ show i]
prettyPrint n (Bin1 s _) = ["%" ++ s]
prettyPrint n (Bin2 s _) = ["%" ++ s]
prettyPrint n (Bin3 s _) = ["%" ++ s]
prettyPrint n (App f xs) = if all (isSmall) (f':xs') then small else large
  where
    f' = prettyPrint n f
    xs' = map (prettyPrint n) xs
    small = parens [intercalate " " (map concat (f':xs'))]
    large = f' ++ indent (concat xs')
prettyPrint n (Lam xs m y) = ("\\" ++ show xs ++" " ++ show m) : indent (prettyPrint (1 + m + length xs) y)
prettyPrint n (Let bs x) = ["let"] ++ indent (concatMap (printB n) ([n..] `zip` bs)) ++ ["in"] ++ 
    indent (prettyPrint (n + length bs) x)
prettyPrint n (LetRec bs x) = ["letrec"] ++ indent (concatMap (printB (n + length bs)) ([n..] `zip` bs)) ++ ["in"] ++ 
    indent (prettyPrint (n + length bs) x)
prettyPrint n (Hash m ls) = if isSmall m' then small else large
  where
    m' = concatMap (printKV n) m
    large = ["@" ++ show ls ++ "{"] ++ indent m' ++ ["}"]
    small = ["@" ++ show ls ++ "{" ++ concat m' ++ "}"]
prettyPrint n (List l) = if isSmall l' then small else large
  where
    l' = concatMap (prettyPrint n) l
    large = ["["] ++ indent l' ++ ["]"]
    small = ["[" ++ concat l' ++ "]"]
prettyPrint n (Mod r _ _ _ x) = if isSmall x' then small else large
  where
    x' = prettyPrint n x
    large = ["mod " ++ r] ++ indent x'
    small = ["mod " ++ r ++ " " ++ concat x']
prettyPrint n (Clr xs m y) = ["Clr"]  
--prettyPrint n (Clr xs m y) = ("Clr " ++ show m) : indent (prettyPrint (1 + m + length xs) y)
prettyPrint n (Cap _ _) = ["Cap"]
prettyPrint n (Cell _) = ["Cell"]

printB n (k, v) = if isSmall v' then small else large
  where
    k' = neg k
    v' = prettyPrint n v
    small = [show k' ++ " = " ++ concat v']
    large = [show k' ++ " ="] ++ indent v'

printKV n (k, v) = if isSmall v' then small else large
  where
    v' = prettyPrint n v
    small = [k ++ " = " ++ concat v']
    large = [k ++ " ="] ++ indent v'

prettyPutStrLn = putStrLn . unlines . prettyPrint 0

isCell (Cell _) = True
isCell _ = False

isWhnf :: Op -> Bool
isWhnf !op = case op of
  Val _ -> True
  Bin1 _ _ -> True
  Bin2 _ _ -> True
  Bin3 _ _ -> True
  Clr _ _ _ -> True
  Hash h _ -> all (\(_, x) -> isCell x || isWhnf x) h
  List l -> all (\x -> isCell x || isWhnf x) l
  Mod {modEx = x} -> isWhnf x
  _ -> False

reduce :: Env -> Op -> Op
reduce !env (App f xs) = case reduce env f of
  b@(Bin1 _ _) -> applyBin1 env b xs
  b@(Bin2 _ _) -> applyBin2 env b xs
  b@(Bin3 _ _) -> applyBin3 env b xs
  c@(Clr _ _ _) -> applyCls env c xs
  x -> error $ "cannot apply " ++ show x ++ " to " ++ show xs
reduce !env (Ref i) = reduce env (mem env i)
reduce !env (Lam xs n y) = Clr (mkEnvSlice $ map (toCellCap env . Ref) xs) n y
reduce !env (Cap ls x) = let env' = envSetLocal' ls env in (reduce env' x)
reduce !env c@(Cell _) = reduceCell env c
reduce !env (Let bs x) = let env' = envAddLocal (map (toCellCap env) bs) env in (reduce env' x)
reduce !env (LetRec bs x) = reduce env' x
  where 
    bs' = map (toCellCap env') bs
    env' = envAddLocal bs' env
reduce !env x = toCellCap env x

reduceCell :: Env -> Op -> Op
reduceCell env (Cell r) = unsafePerformIO $ do
  op <- readIORef r
  if isWhnf op 
    then return op
    else do
      let op' = reduce env op
      writeIORef r op'
      return op'
 
applyBin1, applyBin2, applyBin3, applyCls :: Env -> Op -> [Op] -> Op

applyBin1 env (Bin1 _ b) [x] = reduce env (b env x)
applyBin1 env (Bin1 _ b) (x:xs) = reduce env (App (b env x) xs)

applyBin2 env (Bin2 _ b) [x,y] = reduce env (b env env x y)
applyBin2 env (Bin2 d b) [x] = Bin1 d (\env2 y -> b env env2 x y)
applyBin2 env (Bin2 _ b) (x:y:xs) = reduce env (App (b env env x y) xs)

applyBin3 env (Bin3 _ b) [x,y,z] = reduce env (b env env env x y z)
applyBin3 env (Bin3 d b) [x] = Bin2 d (\env2 env3 y z -> b env env2 env3 x y z)
applyBin3 env (Bin3 d b) [x,y] = Bin1 d (\env3 z -> b env env env3 x y z)
applyBin3 env (Bin3 _ b) (x:y:z:xs) = reduce env (App (b env env env x y z) xs)

{-
  Undersaturated apply:
  App (Clr xs 3 y) [a] = Clr env 2 (App (Clr xs 3 y) [a, -1, -2])
-}
applyCls env c@(Clr xs n y) !args = case length args of
  m | m > n -> let (start, end) = splitAt n args in reduce env (App (applyCls env c start) end)
  m | m == n -> 
    let 
      cappedArgs = {-# SCC "tiger:applyCls:args" #-} (c : map (toCellCap env) args)
      env' = {-# SCC "tiger:applyCls:addLocal" #-} envSetLocal'' cappedArgs xs env
    in (reduce env' y)
  m | m < n -> let n' = n-m in Clr (envGetLocal env) n' (App c (map (toCellCap env) args ++ map (Ref . neg) [1..n']))

force :: Env -> Op -> Op
force env e = force' env (reduce env e)
  where
    force' env (Hash h ls) = Hash (map (\(k, v) -> (k, force env v)) h) ls
    force' env (List l) = List (map (force env) l)
    force' env m@(Mod {modEx = x}) = m {modEx = force env x}
    force' _ x = x

toCellCap :: Env -> Op -> Op
toCellCap !env !x = 
  case x of
    Val _ -> x
    Bin1 _ _ -> x
    Bin2 _ _ -> x
    Bin3 _ _ -> x
    Clr _ _ _ -> x
--    Cap _ _ -> x
    List l -> List (map (toCellCap env) l)
    Hash h ls -> Hash (map (\(k, v) -> (k, toCellCap env v)) h) ls
    Ref i -> {-# SCC "tiger:toCellCap:ref" #-} toCellCap env (mem env i)
    Cell _ -> x
    m@(Mod {modEx = x}) -> m {modEx = toCellCap env x}
    _ -> {-# SCC "tiger:toCellCap:_" #-} mkCell $ Cap ({-# SCC "tiger:toCellCap:getLocal" #-} envGetLocal env) x

asVal :: (Typeable a) => Op -> a
asVal (Val d) = let !x = fromDyn d (error $ "dynCast "{- ++ show d-}) in x
--asVal op = error $ show op ++ " is not a Val!"

val :: (Typeable a) => a -> Op
val a = let !op = Val (toDyn a) in op

numBin2 :: (Typeable a, Typeable b) => 
  (Int -> Int -> a) ->
  (Double -> Double -> b) ->
  String -> Op
numBin2 fi fd n = Bin2 n (\envX envY x y -> app (reduce envX x) (reduce envY y))
  where
    app (Val x) (Val y) | isInt x =
      if isInt y then val $ fi (unDyn x) (unDyn y)
      else val $ fd (fromIntegral (unDyn x :: Int)) (unDyn y)
    app (Val x) (Val y) = 
      if isInt y then val $ fd (unDyn x) (fromIntegral (unDyn y :: Int))
      else val $ fd (unDyn x) (unDyn y)

numDiceBin2 :: (Typeable a, Typeable b, Typeable c) => 
  (Int -> Int -> a) ->
  (Double -> Double -> b) ->
  (Dice -> Dice -> c) ->
  String -> Op
numDiceBin2 fi fd fc n = Bin2 n (\envX envY x y -> app (reduce envX x) (reduce envY y))
  where
    app (Val x) (Val y) | isInt x =
      if isInt y then val $ fi (unDyn x) (unDyn y)
      else if isDouble y then val $ fd (fromIntegral (unDyn x :: Int)) (unDyn y)
      else val $ fc (Dice [] $ unDyn x) (unDyn y)
    app (Val x) (Val y) | isDouble x =
      if isDouble y then val $ fd (unDyn x) (unDyn y)
      else val $ fd (unDyn x) (fromIntegral (unDyn y :: Int))
    app (Val x) (Val y) =
      if isDice y then val $ fc (unDyn x) (unDyn y)
      else val $ fc (unDyn x) (Dice [] $ unDyn y)

get_ = Bin2 "get" (\envK envH k h -> get (reduce envK k) (reduce envH h))
  where
    get (Val k) (Hash kvs _) | dynTypeRep k == stringType = let k' = (fromDyn k (error "") :: String) in
      fromMaybe (error $ "get: could not find " ++ show k' ++ " in " ++ show kvs) $ lookup k' kvs
    get (Val i) (List l) | dynTypeRep i == intType = l !! (unDyn i)
    get k h = error ("k is " ++ show k ++ ", h is " ++ show h)

set_ = Bin3 "set" (\envK envV envH k v h -> set (reduce envK k) (toCellCap envV v) (reduce envH h))
  where
    set (Val k) v (Hash h ls) | dynTypeRep k == stringType = Hash (upsert (fromDyn k (error "")) v (const v) h) ls

keys_ = Bin1 "keys" (\envH h -> keys (reduce envH h))
  where
    keys (Hash h ls) = List (map (val . fst) h)

size_ = Bin1 "size" (\envH h -> size (reduce envH h))
  where
    size (Hash h _) = Val $ toDyn $ (length h :: Int)
    size (List l) = Val $ toDyn $ (length l :: Int)
    size x = error $ "size: expected a Hash but got " ++ show x

head_ (List l) = head l
tail_ (List l) = List $ tail l
cons_ v (List l) = List (v:l)
    
if_ = Bin3 "if" (\envC envT envE c t e -> if (asVal (reduce envC c)) then toCellCap envT t else toCellCap envE e)

addLabel_ (Val l) (Hash h ls) = Hash h ((unDyn l) : ls)

hasLabel_ (Val l) (Hash h ls) = val $ (unDyn l) `elem` ls

merge_ (Hash a la) (Hash b lb) = Hash h l
  where
    l = la `union` lb
    h = foldl (\h (k, v) -> upsert k v (\ov -> merge_ ov v) h) a b
merge_ (List a) (List b) = List (a ++ b)
merge_ a b = b

equals_ (Val a) (Val b) | isBool a && isBool b = val $ (unDyn a :: Bool) == (unDyn b :: Bool)
equals_ (Val a) (Val b) | isInt a && isInt b = val $ (unDyn a :: Int) == (unDyn b :: Int)
equals_ (Val a) (Val b) | isDouble a && isDouble b = val $ (unDyn a :: Double) == (unDyn b :: Double)
equals_ (Val a) (Val b) | isString a && isString b = val $ (unDyn a :: String) == (unDyn b :: String)

addDice_ (Dice ds m) (Dice ds' m') = Dice (ds ++ ds') (m + m')
multDice_ (Dice ds m) (Dice [] m') = Dice (concatMap (replicate m') ds) (m * m')

builtins = {-1-}
  [numDiceBin2 (+) (+) addDice_ "+"
  ,numBin2 (-) (-) "-"
  ,numDiceBin2 (*) (*) multDice_ "*"
  ,numBin2 div (/) "/"
  ,numBin2 (<) (<) "<"
  {-6-}
  ,numBin2 (>) (>) ">"
  ,Bin2 "++" (\envX envY x y -> val ((asVal (reduce envX x) :: String) ++ (asVal (reduce envY y) :: String)))
  ,get_
  ,set_
  ,keys_
  {-11-}
  ,size_
  ,if_
  ,Bin2 "merge" (\envA envB a b -> merge_ (reduce envA a) (reduce envB b))
  ,Bin2 "==" (\envA envB a b -> equals_ (reduce envA a) (reduce envB b))
  ,Bin1 "head" (\envA a -> head_ (reduce envA a))
  {-16-}
  ,Bin1 "tail" (\envA a -> tail_ (reduce envA a))
  ,Bin2 "cons" (\envA envL a l -> cons_ (toCellCap envA a) (reduce envL l))
  ,Bin2 "addLabel" (\envL envH l h -> addLabel_ (reduce envL l) (reduce envH h))
  ,Bin2 "hasLabel" (\envL envH l h -> hasLabel_ (reduce envL l) (reduce envH h))
  ,Bin1 "mkDice" (\envI i -> val $ Dice [asVal (reduce envI i)] 0)
  ,Bin2 "trace" (\envM envX m x -> trace (asVal (reduce envM m)) (toCellCap envX x))]
stdEnv = envSetGlobal builtins emptyEnv

data TransContext = TransContext 
  {localId :: Int
  ,path :: Path
  ,mapping :: [(Path, Int)]
  ,ctxGlobals :: [Op]
  ,loadedModules :: Map.Map String Op}

pathToRef :: TransContext -> Path -> Op
pathToRef ctx p = fromMaybe (throughHashes ctx (pinit p) [plast p]) (fmap Ref $ lookup p $ mapping ctx )

throughHashes :: TransContext -> Path -> [String] -> Op
throughHashes ctx PathNil ks = error $ "not found " ++ show ks ++ " in " ++ show (mapping ctx)
throughHashes ctx p ks = case lookup p (mapping ctx) of
  (Just i) -> mkHashChain (pathToRef ctx (tp' "get")) (Ref i) ks
  Nothing -> throughHashes ctx (pinit p) (plast p : ks)

mkHashChain :: Op -> Op -> [String] -> Op
mkHashChain _ h [] = h
mkHashChain get h (k:ks) = mkHashChain get (App (App get [val k]) [h]) ks

addPathToLocalRef :: TransContext -> Path -> TransContext
addPathToLocalRef ctx p = ctx {mapping = upsert p (-id) (const (-id)) (mapping ctx), localId = id + 1}
  where id = localId ctx

exprToOp :: TransContext -> Expr -> Op
exprToOp _ (Const d) = Val d
exprToOp ctx (Var p) = pathToRef ctx p
exprToOp ctx (IfExpr c t e) = exprToOp ctx (Apply (Apply (Apply (Var (tp' "if")) c) t) e)
exprToOp ctx (Apply f x) = App (exprToOp ctx f) [exprToOp ctx x]
exprToOp ctx (LetExpr p x y) = LetRec [exprToOp ctx' x] (exprToOp ctx' y)
  where ctx' = addPathToLocalRef ctx p
exprToOp ctx l@(Lambda p x) = LetRec exts $ Lam bexts 1 (exprToOp ctx' x)
  where
    ctx' = foldl addPathToLocalRef (ctx {localId = 1}) (p : exsym l)
    exts = map (pathToRef ctx) (exsym l)
    n = localId ctx
    bexts = map (\i -> (-i)) $ take (length $ exsym l) $ [n..]
exprToOp ctx (HashMap m ls) = LetRec vals (Hash h ls)
  where
    keys = map fst m
    n = localId ctx
    h = zip keys $ map (\i -> Ref (-i)) [n..]
    n' = n + length keys
    ctx' = foldl addPathToLocalRef ctx $ map tp' keys
    vals = map (\(k, v) -> exprToOp ctx' v) m
exprToOp ctx (ListExpr l) = List $ map (exprToOp ctx) l
exprToOp ctx (ModList s mods) = List l
  where
    l = map f mods
    f (p, x) = Mod {modEx = exprToOp ctx x', modRoot = s, modSrcs = s `delete` dyns, modKeys = [p], modDeps = deps}
      where
        exs = exsym x
        deps = map (\(PathCons _ p) -> p) . filter (\(PathCons n p) -> n == ('@':s)) $ exs
        dyns = nub . map tail . filter (('@'==) . head) . map (\(PathCons n _) -> n) $ exs
        bs = map (\d -> (d, PathCons ('@':d) PathNil)) dyns
        x' = Lambda (tp' ".bindings") 
          (hashWrap p $ foldr (\(d, p) a -> LetExpr p (Apply (Apply (var "get") (Const $ toDyn d)) (var ".bindings")) a) x bs)
        hashWrap PathNil x = x
        hashWrap PathAll x = x
        hashWrap (PathCons n p) x = HashMap [(n, hashWrap p x)] []

ensureLoaded :: TransContext -> String -> IO TransContext
ensureLoaded ctx n = if Map.member n (loadedModules ctx) 
  then return ctx 
  else do
    m <- parseModule n
    (Hash h [], ctx') <- fromModuleToHash ctx m
    let
      paths = map (tp' . fst) h `zip` [(length (ctxGlobals ctx') + 1)..]
      globs = map snd h 
    return $ ctx' 
      {mapping = mapping ctx' ++ paths
      ,ctxGlobals = ctxGlobals ctx' ++ globs
      ,loadedModules = Map.insert n (Hash h []) (loadedModules ctx')}

fromModuleToHash :: TransContext -> Module -> IO (Op, TransContext)
fromModuleToHash ctx (Module is ds) = do
  ctx' <- foldlM ensureLoaded ctx is
  --putStrLn $ "loaded imports " ++ show (mapping ctx') ++ " " ++ show (ctxGlobals ctx')
  let
    h = exprToOp ctx' (HashMap ds [])
  --putStr "op = "
  --prettyPutStrLn h
  hOpt <- applyOpts (force (envSetGlobal (ctxGlobals ctx') emptyEnv)) prettyPutStrLn (ctxGlobals ctx') h
  let
    h' = force (envSetGlobal (ctxGlobals ctx') emptyEnv) hOpt
    (h'', _) = evalMods (envSetGlobal (ctxGlobals ctx') emptyEnv) h'
  return (h'', ctx')

loadModule :: String -> IO Op
loadModule n = do
  ctx <- ensureLoaded testCtx n
  return $ fromJust $ Map.lookup n (loadedModules ctx)

tp = foldr PathCons PathNil
tp' k = tp [k]

var = Var . tp'

iconst :: Int -> Expr
iconst = Const . toDyn

testCtx = 
  TransContext 
    {localId = 0
    ,path = PathNil
    ,mapping = map btp builtins `zip` [1..]
    ,ctxGlobals = builtins
    ,loadedModules = Map.empty}
  where
    btp (Bin1 d _) = tp' d
    btp (Bin2 d _) = tp' d
    btp (Bin3 d _) = tp' d

setAll :: (Ord k) => [(k, v)] -> [(k, v)] -> [(k, v)]
setAll a b = foldl (\h (k, v) -> upsert k v (const v) h) a b

updateRs :: [(Int, Op)] -> [(Int, Op)] -> [(Int, Op)]
updateRs a b = foldl (updateR True) a b
  where
    updateR t [] u = if t then [u] else []
    updateR _ ((k, _):rs) u@(k', v') | k==k' = (k, v') : updateR False rs u
    updateR t ((k, Ref i):rs) u@(k', v') | i==k' = (k, v') : updateR t rs u
    updateR t (r:rs) u = r : updateR t rs u

neg :: Int -> Int
neg = (0-)

instance Stat (Op, a) where
  keys (Mod {modKeys = k}, _) = k
  deps (Mod {modDeps = d}, _) = d

deleteAll :: (Ord k) => [k] -> Map.Map k v -> Map.Map k v
deleteAll ks m = foldl (\m k -> Map.delete k m) m ks

insertIfAbsentAll :: (Ord k) => [k] -> v -> Map.Map k v -> Map.Map k v
insertIfAbsentAll ks v m = foldl (\m k -> Map.insertWith (\n o -> o) k v m) m ks

evalMods :: Env -> Op -> (Op, Map.Map String [(Op, Map.Map String Op)])
evalMods env (Hash h []) = (Hash h' [], m)
  where
    hm = map (\(k, v) -> let (v', m) = evalMods env v in ((k, v'), m)) h
    h' = map fst hm
    m = Map.unionsWith (++) (map snd hm)
evalMods env (Hash h ls) | "ignoreall" `elem` ls = (Hash h ls, Map.empty)
evalMods env (Hash h ls) | "ignore" `elem` ls = let (Hash h' _, _) = evalMods env (Hash h (delete "ignore" ls)) in (Hash h' ls, Map.empty)
evalMods env (Hash h ls) = if isIgnore then (Hash h ("ignore":ls), Map.empty) else (hash, modMap')
  where
    (Hash h' [], modMap) = evalMods env (Hash h [])
    mods = sortForEval $ concatMap (\l -> fromMaybe [] (Map.lookup l modMap)) ls
    modMap' = Map.map (map (\(m, bs) -> (m, insertIfAbsentAll ls hash bs))) $ deleteAll ls modMap
    hash = foldl apply (Hash h' ls) mods
    isIgnore = let (Hash _ ls) = hash in "ignore" `elem` ls
    apply x (Mod {modEx = m, modRoot = l}, bs) = merge_ x (force env app)
      where
        app = App m [h]
        h = Hash (Map.toList (Map.insertWith (\n o -> o) l x bs)) []
evalMods env (List l) = (List l', m)
  where
    lm = map (evalMods env) l
    l' = map fst lm
    m = Map.unionsWith (++) (map snd lm)
evalMods env m@(Mod {modRoot = k}) = (m, Map.singleton k [(m, Map.empty)])
evalMods env x = (x, Map.empty)


