{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}
module Expressions where

import Data.Dynamic
import Data.HList
import Data.Maybe
import Data.Generics
import Data.List
import Stats

data Expr =
  Apply Expr Expr
  | Const Dynamic
  | Var Path
  | IfExpr Expr Expr Expr
  | Lambda Path Expr
  | LetExpr Path Expr Expr
  | HashMap [(String, Expr)] [String]
  | ListExpr [Expr]
  | ModList String [(Path, Expr)]

data Module = Module {moduleImports :: [String], moduleDefs :: [(String, Expr)]}

instance Show Expr where
  show (Apply f x) = "(Apply " ++ show f ++ " " ++ show x ++ ")"
  show (Const d) = "(Const " ++ show d ++ ")"
  show (Var p) = "(Var " ++ show p ++ ")"
  show (IfExpr c t e) = "(IfExpr " ++ show c ++ " " ++ show t ++ " " ++ show e ++ ")"
  show (Lambda p e) = "(Lambda " ++ show p ++ " " ++ show e ++ ")"
  show (LetExpr p x y) = "(LetExpr " ++ show p ++ " " ++ show x ++ " " ++ show y ++ ")"
  show (HashMap m ls) = "(Hashmap " ++ show m ++ " " ++ show ls ++ ")"
  show (ListExpr l) = "(ListExpr " ++ show l ++ ")"
  show (ModList l ms) = "(ModList " ++ show l ++ " " ++ show ms ++ ")"

exsym :: Expr -> [Path]
exsym (Apply f x) = exsym f `union` exsym x
exsym (Const _) = []
exsym (Var (PathCons "@" PathNil)) = []
exsym (Var p) = [p]
exsym (IfExpr c t e) = exsym c `union` exsym t `union` exsym e
exsym (Lambda p e) = remPath p (exsym e)
exsym (LetExpr p x y) = remPath p (exsym x `union` exsym y)
exsym (HashMap m _) = foldl union [] (map (exsym . snd) m)
exsym (ListExpr l) = foldl union [] (map exsym l)
exsym (ModList _ ms) = filter (\(PathCons n _) -> head n /= '@') $ foldl union [] (map (exsym . snd) ms)

remPath :: Path -> [Path] -> [Path]
remPath p = filter (not . contains p)

upsert :: (Ord k) => k -> v -> (v -> v) -> [(k, v)] -> [(k, v)]
upsert k v _ [] = [(k, v)]
upsert k _ f ((k', v'):m) | k==k' = (k, f v'):m
upsert k v f (kv':m) = kv' : upsert k v f m
