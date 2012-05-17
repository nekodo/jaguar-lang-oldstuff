{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, 
  DeriveDataTypeable #-}
module TigerOptimisations
  (countUses
  ,applyOpts) where

import Control.Monad.Identity
--import Control.Monad.State
--import Data.Dynamic
--import Data.Foldable(foldlM)
import Data.List
--import qualified Data.Map as Map
import Data.Maybe
--import Debug.Trace
--import Data.IORef
--import System.IO.Unsafe

import TigerAST

countUses :: Int -> Op -> Int
countUses n (Ref i) | i==n = 1
countUses n (Lam xs _ _) | elem n xs = 1
countUses n (App f xs) = sum $ map (countUses n) (f:xs)
countUses n (LetRec bs x) = sum $ map (countUses n) (x:bs)
countUses n (Let bs x) = sum $ map (countUses n) (x:bs)
countUses n (Hash h _) = sum $ map (countUses n . snd) h
countUses n (List l) = sum $ map (countUses n) l
countUses n (Mod {modEx = x}) = countUses n x
countUses _ _ = 0

opts = 
  [(deadCodeElim 0, "deadCodeElim")
  ,(mergeApps, "mergeApps")
  ,(mergeLambdas, "mergeLambdas")
  ,(simplifyLets 0, "simplifyLets")
  ,(simplePropagate 0, "simplePropagate")
  ,(etaConversion, "etaConversion")
  ,(propagateGlobals, "propagateGlobal")
  ,(tieRecLambdas 0, "tieRecLambdas")
  ,(betaReduction 0, "betaReduction")]

neg :: Int -> Int
neg = (0-)

--applyOpts :: (Op -> Op) -> (Op -> IO ()) -
applyOpts force pretty globals x = do
  putStr $ "unopt"
  pretty x
  --let evaled = force x
  --putStr $ "unopt-evaled"
  --pretty evaled
  let optPasses = concat $ replicate 10 $ ((inlineGlobals (filter (isBin . snd) ([1..] `zip` globals)), "inlineGlobals") : opts)
  applyOpts' force pretty optPasses x
applyOpts' _ pretty [] x = do
  putStr $ "fully opted"
  pretty x
  return x
applyOpts' force pretty ((o, d):os) x = do
  let 
    x' = o x
    --evaled = force x'
  --putStr $ "after " ++ d
  --pretty x'
  --putStr $ "evaled"
  --pretty evaled
  applyOpts' force pretty os x'

isBin (Bin1 _ _) = True
isBin (Bin2 _ _) = True
isBin (Bin3 _ _) = True
isBin _ = False

{-
  (f x) y ==> f x y
-}
mergeApps :: Op -> Op
mergeApps (App (App f xs) ys) = mergeApps $ App f (xs ++ ys)
mergeApps x = imapOp mergeApps x

{-
  \2 -> \1 -> x ==> \3 -> x 
-}
mergeLambdas :: Op -> Op
mergeLambdas (Lam xs n (Lam ys m a)) = mergeLambdas $ Lam xs (n+m) a'
  where
    innerOffset = 1 + m + length ys
    finalOffset = 1 + n + m + length xs
    argRs = zip (map neg [1..m]) (map neg [(n + 1)..])
    rs = zip (map neg [(m + 1)..]) (map (\y -> if y < neg n then y - m else y) ys) ++ argRs
    a' = shiftReplace innerOffset (finalOffset - innerOffset) rs a
mergeLambdas x = imapOp mergeLambdas x

{-
  letrec a = b in x ==? a is not recursive ==> let a = b in x
-}
simplifyLets :: Int -> Op -> Op
simplifyLets s (LetRec [b] x) | countUses (neg s) b == 0 = simplifyLets s (Let [shiftRef s (-1) b] x)
simplifyLets s op = imapOpSlot simplifyLets s op

{-
  Propagate ref bindings in let and letrec.
  Does not delete dead bindings!
-}
simplePropagate :: Int -> Op -> Op
simplePropagate s (Let bs x) = imapOpSlot simplePropagate s (Let bs x')
  where 
    x' = replaceOps (catMaybes $ map (maybePropagate x) ([s..] `zip` bs)) x
    maybePropagate x (i, b) = if canPropagate i x b then Just (neg i, shiftRef s (length bs) b) else Nothing
    canPropagate _ _ (Ref _) = True
    canPropagate _ _ (Val _) = True
    canPropagate _ _ op | isBin op = True
    canPropagate i x _ = countUses (neg i) x == 1
simplePropagate s (LetRec bs x) = imapOpSlot simplePropagate s (LetRec bs' x')
  where
    x' = replaceOps (catMaybes $ map (maybePropagate bs x) ([s..] `zip` bs)) x
    bs' = map (replaceOps (catMaybes $ map (maybePropagate bs x) ([s..] `zip` bs))) bs
    maybePropagate bs x (i, b) = if canPropagate i bs x b then Just (neg i, b) else Nothing
    canPropagate _ _ _ (Ref _) = True
    canPropagate _ _ _ (Val _) = True
    canPropagate i bs x b = (countUses (neg i) b == 0) && (sum (map (\b -> countUses (neg i) b) (x:bs)) == 1)
simplePropagate s op = imapOpSlot simplePropagate s op

tieRecLambdas :: Int -> Op -> Op
tieRecLambdas s (LetRec bs x) = imapOpSlot tieRecLambdas s $ LetRec (map f (map neg [s..] `zip` bs)) x
  where
    f (i, Lam xs n y) = Lam xs n (replaceRefs [(findSelfRef i (n + 1) xs, 0)] y)
    f (_, x) = x
    findSelfRef i n [] = 0
    findSelfRef i n (x:xs) = if x == i then neg n else findSelfRef i (n + 1) xs
tieRecLambdas s op = imapOpSlot tieRecLambdas s op

{-
  Delete dead (unused) bindings in let and letrec.
-}
deadCodeElim :: Int -> Op -> Op
deadCodeElim s (Let [] x) = deadCodeElim s x
deadCodeElim s (LetRec [] x) = deadCodeElim s x
deadCodeElim s l@(Let bs x) = 
  case findDeadBinding s (length bs) x of
    Just i -> deadCodeElim s (delLetBinding s i l)
    Nothing -> imapOpSlot deadCodeElim s l
  where
    findDeadBinding s n x = find (\i -> isDeadBinding (i + s) x) [0..(n - 1)]
    isDeadBinding s x = countUses (neg s) x == 0
deadCodeElim s l@(LetRec bs x) = 
  case findDeadRecBinding s bs x of
    Just i -> deadCodeElim s (delLetBinding s i l)
    Nothing -> imapOpSlot deadCodeElim s l
  where
    findDeadRecBinding s bs x = find (\i -> isDeadRecBinding (i + s) bs x) [0..(length bs - 1)]
    isDeadRecBinding s bs x = all (\op -> countUses (neg s) op == 0) (x:bs)
deadCodeElim s l@(Lam xs n y) = 
  case deadExternal of
    Just i -> deadCodeElim s (delLamExternal i l)
    Nothing -> imapOpSlot deadCodeElim s l
  where
    deadExternal = find isDeadExternal [0..(length xs - 1)]
    isDeadExternal e = countUses (-n - 1 - e) y == 0
deadCodeElim s op = imapOpSlot deadCodeElim s op

{-
  Performs eta-conversion of lambdas.
-}
etaConversion :: Op -> Op
etaConversion l@(Lam xs 1 a@(App f [arg])) = case arg of
  Ref (-1) | countUses (-1) a == 1 -> etaConversion (replaceRefs (map neg [2..] `zip` xs) f)
  _ -> imapOp etaConversion l
etaConversion l@(Lam xs 1 a@(App f args)) = case last args of
  Ref (-1) | countUses (-1) a == 1 -> 
    App (etaConversion (replaceRefs (map neg [2..] `zip` xs) f)) 
        (map (replaceRefs (map neg [2..] `zip` xs)) $ init args)
  _ -> imapOp etaConversion l
etaConversion l@(Lam xs n a@(App f [Ref i])) =
  if (i == -n) && (countUses i a == 1)
    then Lam xs (n - 1) (shiftRef (n+1) (-1) f)
    else imapOp etaConversion l
etaConversion l@(Lam xs n a@(App f args)) | length args > 1 = case last args of
  Ref i | (i == -n) && (countUses i a == 1) -> 
    etaConversion (Lam xs (n-1) (App (shiftRef (n+1) (-1) f) (map (shiftRef (n+1) (-1)) (init args))))
  _ -> imapOp etaConversion l
etaConversion op = imapOp etaConversion op

{-
  Performs beta-reduction of lambdas.
  UNFINISHED, does not handle unsaturated applies.
-}
betaReduction :: Int -> Op -> Op
betaReduction s (App l@(Lam xs n y) args) | (not $ isRecLam l) && (n == length args) = Let (args ++ map Ref xs) (shiftRef 1 (s - 1) y)
betaReduction s (App l@(Lam xs n y) args) | (not $ isRecLam l) && (n < length args) = 
  betaReduction s (App (betaReduction s (App (Lam xs n y) (take n args))) (drop n args))
--betaReduction s (App (Lam xs n y) args) = betaReduction s ()
betaReduction s op = imapOpSlot betaReduction s op

isRecLam :: Op -> Bool
isRecLam l@(Lam _ _ y) = countUses 0 y > 0
isRecLam _ = False

{- 
  Propagates globals into lambdas.
-}
propagateGlobals :: Op -> Op
propagateGlobals (Lam xs n y) = Lam xs n (propagateGlobals y')
  where
    globals = filter ((>0) . snd) $ (map neg [(n + 1)..] `zip` xs)
    y' = replaceRefs globals y
propagateGlobals op = imapOp propagateGlobals op

{-
  Inlines globals from the given set into the code.
  Touches only refs, but descends into lambdas.
-}

inlineGlobals :: [(Int, Op)] -> Op -> Op
inlineGlobals rs (Ref i) = case lookup i rs of
  Just op -> op
  Nothing -> Ref i
inlineGlobals rs op = imapOp (inlineGlobals rs) op

{- HELPERS -}

{-
App Op [Op] -- function application
| Val Dynamic -- a constant packed in Dynamic
| Ref Int -- reference to a slot
| Lam [Int] Int Op -- lambda definition, declares external symbols as slots
| Bin1 String (Env -> Op -> Op) -- builtin unary function
| Bin2 String (Env -> Op -> Op -> Op) -- builtin binary function
| Bin3 String (Env -> Op -> Op -> Op -> Op) -- builtin ternary function
| Hash [(String, Op)] -- a map data structure
| LetRec [Op] Op -- recursive let binding
-}
mapOp :: (Monad m) => (Op -> m Op) -> Op -> m Op
mapOp processStage (App f xs) = do
  f' <- processStage f
  xs' <- mapM processStage xs
  return $ App f' xs'
mapOp _ v@(Val _) = return v
mapOp _ r@(Ref _) = return r
mapOp processStage (Lam xs n y) = do
  y' <- processStage y
  return $ Lam xs n y'
mapOp _ b@(Bin1 _ _) = return b  
mapOp _ b@(Bin2 _ _) = return b
mapOp _ b@(Bin3 _ _) = return b
mapOp processStage (Hash h ls) = do
  h' <- mapM mapKV h
  return $ Hash h' ls
  where
    mapKV (k, v) = do
      v' <- processStage v
      return (k, v')
mapOp processStage (List l) = do
  l' <- mapM processStage l
  return $ List l'
mapOp processStage (Let bs x) = do
  bs' <- mapM processStage bs
  x' <- processStage x
  return $ Let bs' x'
mapOp processStage (LetRec bs x) = do
  bs' <- mapM processStage bs
  x' <- processStage x
  return $ LetRec bs' x'
mapOp processStage m@(Mod {modEx = x}) = do
  x' <- processStage x
  return $ m {modEx = x'}

imapOp f op = runIdentity $ mapOp (return . f) op

mapOpSlot :: (Monad m) => (Int -> Op -> m Op) -> Int -> Op -> m Op
mapOpSlot processStage s (App f xs) = do
  f' <- processStage s f
  xs' <- mapM (processStage s) xs
  return $ App f' xs'
mapOpSlot _ _ v@(Val _) = return v
mapOpSlot _ _ r@(Ref _) = return r
mapOpSlot processStage _ (Lam xs n y) = do
  y' <- processStage (1 + n + length xs) y
  return $ Lam xs n y'
mapOpSlot _ _ b@(Bin1 _ _) = return b  
mapOpSlot _ _ b@(Bin2 _ _) = return b
mapOpSlot _ _ b@(Bin3 _ _) = return b
mapOpSlot processStage s (Hash h ls) = do
  h' <- mapM mapKV h
  return $ Hash h' ls
  where
    mapKV (k, v) = do
      v' <- processStage s v
      return (k, v')
mapOpSlot processStage s (List l) = do
  l' <- mapM (processStage s) l
  return $ List l'
mapOpSlot processStage s (Let bs x) = do
  bs' <- mapM (processStage s) bs
  x' <- processStage (s + length bs) x
  return $ Let bs' x'
mapOpSlot processStage s (LetRec bs x) = do
  let s' = s + length bs
  bs' <- mapM (processStage s') bs
  x' <- processStage s' x
  return $ LetRec bs' x'
mapOpSlot processStage s m@(Mod {modEx = x}) = do
  x' <- processStage s x
  return $ m {modEx = x'}
  
imapOpSlot f s op = runIdentity $ mapOpSlot (\s op -> return $ f s op) s op

{- Shifts all refs equal to or greater than a specified number by x. -}
shiftRef :: Int -> Int -> Op -> Op
shiftRef n x (Ref i) | i <= neg n = Ref (i - x)
shiftRef n x (Lam xs m op) = Lam (map (\i -> if i <= neg n then i - x else i) xs) m op
shiftRef n x op = runIdentity $ mapOp (return . shiftRef n x) op

addLetBinding :: Int -> Op -> Op -> Op
addLetBinding n b (Let bs x) = Let (bs ++ [b]) (shiftRef (n + length bs) 1 x)
addLetBinding n b (LetRec bs x) = LetRec (bs' ++ [b]) x'
  where
    x' = shiftRef (n + length bs) 1 x
    bs' = map (shiftRef (n + length bs) 1) bs

deleteIndex :: Int -> [a] -> [a]
deleteIndex i = map snd . filter ((/= i) . fst) . zip [0..]

delLetBinding :: Int -> Int -> Op -> Op
delLetBinding n b (Let bs x) = Let (deleteIndex b bs) (shiftRef (n + b) (-1) x)
delLetBinding n b (LetRec bs x) = LetRec bs' x'
  where
    x' = shiftRef (n + b) (-1) x
    bs' = map (shiftRef (n + b) (-1)) (deleteIndex b bs)

delLamExternal :: Int -> Op -> Op
delLamExternal i (Lam xs n y) = Lam (deleteIndex i xs) n (shiftRef (n + 1 + i) (-1) y)

replaceRefs :: [(Int, Int)] -> Op -> Op
replaceRefs rs (Ref i) = case lookup i rs of
  Just r -> Ref r
  Nothing -> Ref i
replaceRefs rs (Lam xs m op) = Lam (map f xs) m op
  where 
    f i = case lookup i rs of
      Just r -> r
      Nothing -> i
replaceRefs rs op = runIdentity $ mapOp (return . replaceRefs rs) op

shiftReplace :: Int -> Int -> [(Int, Int)] -> Op -> Op
shiftReplace n x _ (Ref i) | i <= neg n = Ref (i - x)
shiftReplace _ _ rs (Ref i) = case lookup i rs of
  Just r -> Ref r
  Nothing -> Ref i
shiftReplace n x rs (Lam xs m op) = Lam (map f xs) m op
  where
    f i | i <= neg n = i - x
    f i = case lookup i rs of
      Just r -> r
      Nothing -> i
shiftReplace n x rs op = runIdentity $ mapOp (return . shiftReplace n x rs) op

replaceOps :: [(Int, Op)] -> Op -> Op
replaceOps rs (Ref i) = case lookup i rs of
  Just op -> op
  Nothing -> Ref i
replaceOps rs (Lam xs m op) = Lam (map f xs) m (if null propagables then op else op')
  where 
    f i = case lookup i rs of
      Just (Ref r) -> r
      _ -> i
    propagables = catMaybes $ map isPropagable rs
    op' = Let (map snd propagables) (replaceRefs (map fst propagables `zip` map neg [(m + length xs + 1)..]) $ shiftRef (m + length xs + 1) (length propagables) op)
    isPropagable (i, op) = case lookup i (xs `zip` map neg [(m + 1)..]) of
      Just x | hasNoDeps op -> Just (x, op)
      _ -> Nothing
    hasNoDeps op | isBin op = True
    hasNoDeps (Val _) = True
    hasNoDeps (Lam [] _ _) = True
    hasNoDeps _ = False
replaceOps rs op = runIdentity $ mapOp (return . replaceOps rs) op
