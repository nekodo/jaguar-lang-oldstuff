{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}
module Expressions where

import Data.Dynamic
import Data.HList
import Data.Maybe
import Data.Generics
import Data.List
import Stats

type PathExpr = [(Path, Dynamic)] -> [(Path, Dynamic)]

getCast :: (Typeable a) => Path -> [(Path, Dynamic)] -> a
getCast k = fromJust . join . fmap fromDynamic . lookup k

force :: (Typeable a) => Dynamic -> a
force d = fromDyn d (error $ "dyn cast: " ++ show d)

class Expressible a where
  asExpr :: a -> PathExpr
  getDeps :: a -> [Path]
  getKeys :: a -> [Path]

asStat :: (Expressible a) => a -> Stat
asStat a = Stat {deps = getDeps a, keys = getKeys a, evaluator = asExpr a}

class (HList l) => Homogenous a l where
  asList :: l -> [a]

instance Homogenous a HNil where
  asList _ = []

instance (Homogenous a l) => Homogenous a (HCons a l) where
  asList (HCons a l) = a : asList l

instance (Typeable x) => Expressible (HCons Path HNil, x) where
  asExpr (HCons p HNil, x) = \m -> [(p, toDyn x)]
  getDeps _ = []
  getKeys (HCons p HNil, _) = [p]

instance (Typeable a, Expressible (p, b), Homogenous Path p) => Expressible (HCons Path p, a -> b) where
  asExpr (HCons p ps, f) = \m -> let b = f (getCast p m) in asExpr (ps, b) m
  getDeps = init . asList . fst
  getKeys = (:[]) . last . asList . fst

dummyStats3 =
  [asStat (HCons a HNil, 3 :: Int)
  ,asStat (HCons a (HCons b HNil), (*2) :: Int -> Int)
  ,asStat (HCons a (HCons b (HCons c HNil)), (+) :: Int -> Int -> Int)]
 where
  a = PathCons "a" PathNil
  b = PathCons "b" PathNil
  c = PathCons "c" PathNil

data Expr =
  Apply Expr Expr
  | Const Dynamic
  | Var Path
  | IfExpr Expr Expr Expr
  | Builtin (Env -> Expr -> Expr)
  | Lambda Path Expr
  | LetExpr Path Expr Expr
  | HashMap [(String, Expr)]
  | Closure Env Expr

instance Show Expr where
  show (Apply f x) = "(Apply " ++ show f ++ " " ++ show x ++ ")"
  show (Const d) = "(Const " ++ showDynamic d ++ ")"
  show (Var p) = "(Var " ++ show p ++ ")"
  show (IfExpr c t e) = "(IfExpr " ++ show c ++ " " ++ show t ++ " " ++ show e ++ ")"
  show (Builtin _) = "(Builtin ?)"
  show (Lambda p e) = "(Lambda " ++ show p ++ " " ++ show e ++ ")"
  show (LetExpr p x y) = "(LetExpr " ++ show p ++ " " ++ show x ++ " " ++ show y ++ ")"
  show (HashMap m) = "(Hashmap " ++ show m ++ ")"

exsym :: Expr -> [Path]
exsym (Apply f x) = exsym f `union` exsym x
exsym (Const _) = []
exsym (Var (PathCons "@" PathNil)) = []
exsym (Var p) = [p]
exsym (IfExpr c t e) = exsym c `union` exsym t `union` exsym e
exsym (Builtin _) = []
exsym (Lambda p e) = delete p (exsym e)
exsym (LetExpr p x y) = delete p (exsym x `union` exsym y)
exsym (HashMap m) = foldl union [] (map (exsym . snd) m)

evalConst :: Env -> Expr -> Dynamic
evalConst _ (Const d) = d
evalConst m e = eval2 m (exprEval m e)
  where
    eval2 _ (Const d) = d
    eval2 _ _ = error "does not eval to const!"

asInt :: Expr -> Int
asInt (Const d) = force d

type Env = [(String, Expr)]

lookupFun :: Path -> Env -> Expr
lookupFun p m = either (const $ either error id (lookupF (PathCons ".builtin" p) m)) id (lookupF p m)

lookupF :: Path -> Env -> Either String Expr
lookupF PathAll m = Right $ HashMap m
lookupF PathNil m = Right $ HashMap m
lookupF (PathCons k p) m = case (lookup k m) of
  Just (HashMap m') -> lookupF p m'
  Just e | p == PathNil -> Right e
  Just e -> Left $ "cannot descend into " ++ show e
  Nothing -> Left $ "did not find " ++ k

updateFun :: Path -> Expr -> Env -> Env
updateFun (PathCons k PathNil) e m = upsert k e (const e) m
updateFun (PathCons k p) e m = upsert k (HashMap $ updateFun p e []) upd m
  where
    upd (HashMap m) = HashMap $ updateFun p e m
    upd _ = error "not a hashmap"

upsert :: (Ord k) => k -> v -> (v -> v) -> [(k, v)] -> [(k, v)]
upsert k v _ [] = [(k, v)]
upsert k _ f ((k', v'):m) | k==k' = (k, f v'):m
upsert k v f (kv':m) = kv' : upsert k v f m

exprEval :: Env -> Expr -> Expr
exprEval m (IfExpr c t e) = if (force (evalConst m c) :: Bool) then exprEval m t else exprEval m e
exprEval m (Var p) = exprEval m $ lookupFun p m
exprEval m (Apply (Builtin f) x) = f m (exprEval m x)
exprEval m (Apply l@(Lambda p e) x) = exprEval (updateFun (PathCons "@" PathNil) l m) (LetExpr p x e)
exprEval m (Apply f x) = exprEval m (Apply (exprEval m f) x)
exprEval m (LetExpr p l@(Lambda _ _) y) = exprEval (updateFun p (bindClosure (Just p) m l) m) y
exprEval m (LetExpr p x y) = exprEval (updateFun p (exprEval m x) m) y
exprEval m l@(Lambda _ _) = bindClosure Nothing m l
exprEval m (HashMap h) = HashMap $ map (\(k, v) -> (k, exprEval m v)) h
exprEval _ e = e

bindClosure :: Maybe Path -> Env -> Expr -> Expr
bindClosure self m l@(Lambda p e) = Lambda p e'
  where
    closure = case self of
      Just self -> (self, Var (PathCons "@" PathNil)) : map (\p -> (p, lookupFun p m)) (delete self $ exsym l)
      Nothing -> map (\p -> (p, lookupFun p m)) (exsym l)
    e' = asLets closure
    asLets [] = e
    asLets ((k, v):ls) = LetExpr k v (asLets ls)

class Expressible2 a where
  asExpr2 :: a -> Expr

instance (Typeable a) => Expressible2 (HZero, a) where
  asExpr2 = Const . toDyn . snd

instance (Typeable a, HNat n, Expressible2 (n, b)) => Expressible2 (HSucc n, a -> b) where
  asExpr2 (n, f) = Builtin (\m x -> asExpr2 (hPred n, f (force $ evalConst m x)))

hOne = hSucc hZero
hTwo = hSucc hOne

size_ :: Expr -> Expr
size_ (HashMap m) = Const . toDyn . toInteger . length $ m

set_ :: Expr -> Expr -> Expr -> Expr
set_ (Const k) v (HashMap m) = HashMap $ upsert k' v (const v) m
  where k' = fromJust $ (fromDynamic k :: Maybe String) `orElse` fmap show (fromDynamic k :: Maybe Integer)

get_ :: Expr -> Expr -> Expr
get_ (Const k) (HashMap m) = fromJust $ lookup k' m
  where k' = fromJust $ (fromDynamic k :: Maybe String) `orElse` fmap show (fromDynamic k :: Maybe Integer)

keys_ :: Expr -> Expr
keys_ (HashMap m) = HashMap $ map (\(i, (k, _)) -> (show i, Const (toDyn k))) $ zip [0..] m

builtins :: [(String, Expr)]
builtins =
  [("+", asExpr2 (hTwo, (+) :: Integer -> Integer -> Integer))
  ,("-", asExpr2 (hTwo, (-) :: Integer -> Integer -> Integer))
  ,("<", asExpr2 (hTwo, (<) :: Integer -> Integer -> Bool))
  ,(">", asExpr2 (hTwo, (>) :: Integer -> Integer -> Bool))
  ,("&&", asExpr2 (hTwo, (&&) :: Bool -> Bool -> Bool))
  ,("||", asExpr2 (hTwo, (||) :: Bool -> Bool -> Bool))
  ,("!", asExpr2 (hOne, not :: Bool -> Bool))
  ,("size", Builtin (const size_))
  ,("set", Builtin (\_ k -> Builtin (\_ v -> Builtin (\_ h -> set_ k v h))))
  ,("get", Builtin (\_ k -> Builtin (\_ h -> get_ k h)))
  ,("keys", Builtin (const keys_))]
