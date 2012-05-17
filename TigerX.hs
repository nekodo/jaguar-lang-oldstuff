{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, RankNTypes, FlexibleContexts, MultiParamTypeClasses, TypeFamilies #-}

module TigerX where
  
import Data.Dynamic
import Data.IORef
import Data.List
import Data.Maybe

neg :: Int -> Int
neg = (0-)

upsert :: (Ord k) => k -> v -> (v -> v) -> [(k, v)] -> [(k, v)]
upsert k v _ [] = [(k, v)]
upsert k _ f ((k', v'):m) | k==k' = (k, f v'):m
upsert k v f (kv':m) = kv' : upsert k v f m

class (Ord r) => Slot r where
  isGlobal :: r -> Bool
  data SlotMap r
  getBinding :: r -> SlotMap r -> Op r
  setBinding :: r -> Op r -> SlotMap r -> (SlotMap r, Op r -> Op r)
  setBindings :: [(r, Op r)] -> SlotMap r -> (SlotMap r, Op r -> Op r)
  setBindings bs m = foldl (\(m, f) (r, op) -> let (m', g) = setBinding r op m in (m', g . f)) (m, id) bs
--  mapBindings :: (r -> Op r -> Op r) -> SlotMap r -> SlotMap r
--  filterBindings :: (r -> Op r -> Bool) -> SlotMap r -> (SlotMap r, Op r -> Op r)
  allBindings :: SlotMap r -> [(r, Op r)]
  data SlotList r
  mapSlotList :: (r -> r) -> SlotList r -> SlotList r
  asList :: SlotList r -> [r]

instance Slot Int where
  isGlobal = (> 0)
  data SlotMap Int = SlotMapInt {smiOffset :: Int, smiBs :: [Op Int]}
  getBinding i (SlotMapInt n bs) = let i' = abs i - n in bs !! i'
  setBinding i op (SlotMapInt n bs) =
    if i' >= 0 && i' < length bs
      then (SlotMapInt n (take i' bs ++ (op : drop (i' + 1) bs)), id)
      else (SlotMapInt n (bs ++ [op]), transformRefs (\x -> if x == i then r else if x >= r then x + 1 else x))
    where
      i' = abs i - n
      r = n + length bs    
--  mapBindings :: (r -> Op r -> Op r) -> SlotMap r -> SlotMap r
--  filterBindings :: (r -> Op r -> Bool) -> SlotMap r -> (SlotMap r, Op r -> Op r)
  allBindings (SlotMapInt n bs) = [n..] `zip` bs
  data SlotList Int = SlotListInt [Int] | SlotListIntSpan Int Int
  mapSlotList f (SlotListInt l) = SlotListInt (map f l)
  asList (SlotListInt l) = l
  asList (SlotListIntSpan n m) = [n..m]

transformRefs :: (Slot r) => (r -> r) -> Op r -> Op r
trasnformRefs f (Lam ex ps b) = Lam (mapSlotList f ex) ps b
transformRefs f (Ref r) = Ref (f r)
transformRefs f (App g args) = App (transformRefs f g) (map (transformRefs f) args)
transformRefs f (Hash h) = Hash (map (\(k, op) -> (k, transformRefs f op)) h)
transformRefs f x = x

instance Slot String where
  isGlobal = ('@'==) . head
  data SlotMap String = SlotMapString [(String, Op String)]
  getBinding s (SlotMapString bs) = fromJust $ lookup s bs
  setBinding s op (SlotMapString bs) = (SlotMapString $ upsert s op (const op) bs, id)
--  mapBindings :: (r -> Op r -> Op r) -> SlotMap r -> SlotMap r
--  filterBindings :: (r -> Op r -> Bool) -> SlotMap r -> (SlotMap r, Op r -> Op r)
  allBindings (SlotMapString bs) = bs
  data SlotList String = SlotListString [String]
  mapSlotList f (SlotListString l) = SlotListString (map f l)
  asList (SlotListString l) = l

data (Slot r) => Env r = Env {global ::  SlotMap r, local :: SlotMap r}
--type Env = ()

data (Slot r) => Op r =
  App {appFun :: Op r, appArgs :: [Op r]} -- function application
  | Val Dynamic -- a constant packed in Dynamic
  | Ref r -- reference to a slot
  | Lam {lamEx :: SlotList r, lamParams :: SlotList r, lamBody :: Op r} -- lambda definition, declares external symbols as slots
  | Bin1 String (Env r -> Op r -> Op r) -- builtin unary function
  | Bin2 String (Env r -> Op r -> Op r -> Op r) -- builtin binary function
  | Bin3 String (Env r -> Op r -> Op r -> Op r -> Op r) -- builtin ternary function
  | Hash [(String, Op r)] -- a map data structure
  | Let {letBs :: SlotMap r, letBody :: Op r} -- non-recursive let binding
  | LetRec {letRecBs :: SlotMap r, letRecBody :: Op r} -- recursive let binding
  -- runtime only
  | Clr {clrEnv :: SlotMap r,  clrParams :: SlotList r, clrBody :: Op r} -- a closure of a lambda
  | Cap {capEnv :: SlotMap r, capBody :: Op r} -- a closure of an expression
  | Cell (IORef (Op r)) -- wraps an expression to allow results of lazy evaluation


--intify (Slot r) :: Op r -> Op Int
--intify (Val d) = Val d
--intify (App f x) = App (intify )
{-
mapOp :: (Monad m, Slot r, Slot s) => (Op r -> m (Op s)) -> Op r -> m (Op s)
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
mapOp processStage (LetRec bs x) = do
  bs' <- mapM processStage bs
  x' <- processStage x
  return $ LetRec bs' x'

-}




