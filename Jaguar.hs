{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, DeriveDataTypeable, BangPatterns #-}
module Jaguar where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Data.Dynamic
import Data.Maybe
import qualified Data.Map as M

import Stats(Path)

type Symbol = String

data Expr =
  Ref {refSym :: Symbol, refType :: Type}
  | Val {valVal :: Dynamic, valType :: Type}
  | App {appFun :: Expr, appArg :: Expr, appType :: Type}
  | Lam {lamParam :: Symbol, lamParamType :: Type, lamBody :: Expr, lamType :: Type}
  | Let {letBs :: [(Symbol, Expr)], letBody :: Expr}
  | LetRec {letRecBs :: [(Symbol, Expr)], letRecBody :: Expr}
  | Mod {modRoot :: String, modSrcs :: [String], modDeps :: [Path], modKeys :: [Path], modEx :: Expr} -- stat mod
  deriving (Show)

data Type = 
  NoType
  | TypeBot
  | TypeConst Symbol
  | TypeApp Type Type
--  | TypeDynamic
  | TypeVar String
  deriving (Show, Eq)

stringType = typeOf (error "" :: String)
intType = typeOf (error "" :: Int)
integerType = typeOf (error "" :: Integer)
boolType = typeOf (error "" :: Bool)
doubleType = typeOf (error "" :: Double)
--diceType = typeOf (error "" :: Dice)

isString = (stringType ==) . dynTypeRep
isInt = (intType ==) . dynTypeRep
isInteger = (integerType ==) . dynTypeRep
isBool = (boolType ==) . dynTypeRep
isDouble = (doubleType ==) . dynTypeRep
--isDice = (diceType ==) . dynTypeRep

lub :: Type -> Type -> Type
lub NoType t = t
lub TypeBot _ = TypeBot
--lub TypeDynamic t' = t'
lub t@(TypeConst n) t' = case t' of
  TypeBot -> t
--  TypeDynamic -> t
  NoType -> t
  TypeConst n' | n==n' -> t
  _ -> error $ "no LUB for " ++ show t ++ " and " ++ show t'
lub t t' = error $ "no LUB for " ++ show t ++ " and " ++ show t'
  
getType :: Expr -> Type
getType e = case e of
  Ref {refType = t} -> t
  Val {valType = t} -> t
  Lam {lamType = t} -> t
  App {appType = t} -> t
  Let {letBody = x} -> getType x
  LetRec {letRecBody = x} -> getType x
  Mod {} -> TypeConst "Mod"

setType :: Type -> Expr -> Expr
setType t e = case e of
  r @ Ref {} -> r {refType = t}
  v @ Val {} -> v {valType = t}
  l @ Lam {} -> l {lamType = t}
  a @ App {} -> a {appType = t}
  _ -> e

constrainTypeToLub :: Expr -> Type -> Expr
constrainTypeToLub e t = setType (lub t (getType e)) e

dynType :: Dynamic -> Type
dynType d | isString d = TypeConst "String"
dynType d | isBool d = TypeConst "Bool"
dynType d | isInt d = TypeConst "Int"
dynType d | isInteger d = TypeConst "Integer"
dynType d | isDouble d = TypeConst "Double"

nameGen i = ("t" ++ show i) : nameGen (i + 1)
names = nameGen 1

freshName = do
  (n:ns) <- get
  put ns
  return n

replaceNoTypeWithTypeVar :: Type -> State [Symbol] Type
replaceNoTypeWithTypeVar t = case t of
  NoType -> fmap TypeVar freshName
  _ -> mapType replaceNoTypeWithTypeVar t

eliminateNoType :: Expr -> State [Symbol] Expr
eliminateNoType = mapExprType replaceNoTypeWithTypeVar
  
data TypeEq =
  TEQ Type Type
  | LUB Type Type
  | SUB Type Type -- SUB a b = a <: b
  deriving (Show, Eq)

inferEqs :: M.Map Symbol Type -> Expr -> [TypeEq]
inferEqs bindings e =
  case e of
    Ref s t@(TypeVar n) -> [TEQ (prefixTypeVars n $ bindings M.! s) t]
    Val d t -> [TEQ (dynType d) t]
    App f a t -> concatMap (inferEqs bindings) [f, a] ++ [TEQ (getType f) (TypeApp (TypeApp (TypeConst "Fun") (getType a)) t)]
    Lam p pt b t -> inferEqs (M.insert p pt bindings) b ++ [TEQ t (TypeApp (TypeApp (TypeConst "Fun") pt) (getType b))]
    Let bs x -> let bindings' = M.fromList (map (\(s, e) -> (s, getType e)) bs) `M.union` bindings in
      concatMap (inferEqs bindings . snd) bs ++ inferEqs bindings' x
    LetRec bs x ->   let bindings' = M.fromList (map (\(s, e) -> (s, getType e)) bs) `M.union` bindings in
        concatMap (inferEqs bindings' . snd) bs ++ inferEqs bindings' x
    e @ Mod {modEx = x} -> inferEqs bindings x

prefixTypeVars :: String -> Type -> Type
prefixTypeVars p t = case t of
  TypeVar n -> TypeVar $ p ++ "$" ++ n
  _ -> applyIdent mapType (prefixTypeVars p) t

{-
  no, bot, const, var, app
  EQ,SUB no _ = error
  EQ,SUB x x = ()
  EQ bot _ = error
  EQ constA constB = if constA!=constB then error else ()
  EQ const app = error
  EQ const var = var -> const
  EQ varA varB = varA -> varB
  EQ var app = var -> app
  EQ (app a b) (app c d) = EQ a c, EQ b d
  
  SUB bot _ = ()
  SUB _ bot = error
  SUB const _ = error
  SUB _ const = error
  SUB var _ = EQ var _
  SUB _ var = ()
  SUB (app a b) (app c d) = 
-}

solveEq :: TypeEq -> ([(Symbol, Type)], [TypeEq])
solveEq (TEQ NoType _) = error "NoType"
solveEq (TEQ _ NoType) = error "NoType"
solveEq (TEQ x y) | x==y = ([], [])
solveEq (TEQ TypeBot _) = error "TypeBot"
solveEq (TEQ _ TypeBot) = error "TypeBot"
solveEq (TEQ (TypeVar s) x) = ([(s, x)], [])
solveEq (TEQ x (TypeVar s)) = ([(s, x)], [])
solveEq (TEQ (TypeApp a b) (TypeApp c d)) = ([], [TEQ a c, TEQ b d])
solveEq eq = error $ "error " ++ show eq

solveEqsWorker :: [TypeEq] -> [(Symbol, Type)] -> [(Symbol, Type)]
solveEqsWorker [] subs = subs
solveEqsWorker (eq:eqs) subs = solveEqsWorker (eqs' ++ neqs) (subs' ++ nsubs)
  where
    (nsubs, neqs) = solveEq eq
    eqs' = map (substituteEq nsubs) eqs
    subs' = map (\(s, t) -> (s, substituteType nsubs t)) subs
    
solveEqs eqs = solveEqsWorker eqs []

substituteEq nsubs (TEQ a b) = TEQ (substituteType nsubs a) (substituteType nsubs b)

substituteType nsubs t = case t of
  TypeVar n -> case lookup n nsubs of
    Just t -> t
    Nothing -> t
  _ -> applyIdent mapType (substituteType nsubs) t

applySubs subs e = applyIdent mapExprType (substituteType subs) e

inferTypes :: Expr -> Expr
inferTypes e = 
  let e' = evalState (eliminateNoType e) names
      eqs = inferEqs M.empty e'
      subs = solveEqs eqs
  in applySubs subs e'


mapExpr :: (Monad m) => (Expr -> m Expr) -> Expr -> m Expr
mapExpr mapper e = 
  case e of
    Ref {} -> return e
    Val {} -> return e
    App f a t -> do
      f' <- mapper f
      a' <- mapper a
      return $ App f' a' t
    Lam p pt b t -> do
      b' <- mapper b
      return $ Lam p pt b' t
    Let bs x -> do
      bs' <- mapM (\(k, v) -> mapper v >>= (\v' -> return (k, v'))) bs
      x' <- mapper x
      return $ Let bs' x'
    LetRec bs x -> do
      bs' <- mapM (\(k, v) -> mapper v >>= (\v' -> return (k, v'))) bs
      x' <- mapper x
      return $ LetRec bs' x'
    e @ Mod {modEx = x} -> do
      x' <- mapper x
      return $ e {modEx = x'}

--applyIdent :: (Monad m) => ((a -> m a) -> b -> m b) -> (a -> a) -> b -> b
applyIdent f g x = runIdentity (f (\y -> return $ g y) x)

mapType :: (Monad m) => (Type -> m Type) -> Type -> m Type
mapType f t = case t of
  TypeApp t a -> do
    t' <- f t
    a' <- f a
    return $ TypeApp t' a'
  _ -> return t

mapExprType :: (Monad m) => (Type -> m Type) -> Expr -> m Expr
mapExprType f (Lam p pt b t) = do
  pt' <- f pt
  t' <- f t
  b' <- mapExprType f b
  return $ Lam p pt' b' t'
mapExprType f e = do
  t <- f (getType e)
  mapExpr (mapExprType f) (setType t e)

data Context = Context 
  {symbols :: [Symbol]
  ,bindings :: [(Symbol, Expr)]
  ,mapFun :: Expr -> Ctx Expr}
type Ctx = State Context

freshId :: Ctx Symbol
freshId = do
  s <- get
  put $ s {symbols = tail (symbols s)}
  return $ head (symbols s)

descend :: Expr -> Ctx Expr
descend e = do
  ctx <- get
  mapExpr (mapFun ctx) e

postTraverse f e = do
  e' <- descend e
  f e'

preTraverse f e = do
  e' <- f e
  descend e'

start s f e = evalState (f e) (Context s [] f)

test1 = Val (toDyn (6 :: Int)) NoType
test2 = Let [("x", test1)] (Ref "x" NoType)
test3 = Lam "x" NoType (Ref "x" NoType) NoType
test4 = LetRec [("f", test3)] (App (Ref "f" NoType) (Val (toDyn (10 :: Int)) NoType) NoType)
test5 = LetRec [("f", Lam "x" NoType (App (Ref "f" NoType) (Ref "x" NoType) NoType) NoType)] (App (Ref "f" NoType) (Val (toDyn (10 :: Int)) NoType) NoType)

{-
  App a b -> Let x1 a (Let x2 b (App x1 x2))
  Lam p b -> 
-}
{-normalise :: [Symbol] -> Expr -> Expr
normalise s e = start s (postTraverse normalise') e
 
normalise' :: Expr -> Ctx Expr
normalise' x = case x of
  a @ App {appFun = f} | isNotRef f -> do
    n <- freshId
    normalise' $ Let n f (a {appFun = Ref n (getType f)})
  a @ App {appArg = x} | isNotRef x -> do
    n <- freshId
    normalise' $ Let n x (a {appFun = Ref n (getType x)})
  l @ Let {letBs = bs, letBody = x} | isNotRef x -> do
    n <- freshId
    return $ l {letBs = (n, x) : bs, letBody = Ref n (getType x)}
  l @ LetRec   {letRecBs = bs, letRecBody = x} | isNotRef x -> do
    n <- freshId
    return $ l {letBs = (n, x) : bs, letBody = Ref n (getType x)}
  _ -> return x

isNotRef x = case x of
  Ref {} -> False
  _ -> True-}
