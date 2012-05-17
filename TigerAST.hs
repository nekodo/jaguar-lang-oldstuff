{-# LANGUAGE BangPatterns, DeriveDataTypeable #-}

module TigerAST
  (Op(App, Val, Ref, Lam, Bin1, Bin2, Bin3, Hash, List, Let, LetRec, Mod, Clr, Cap, Cell)
  ,modEx
  ,modRoot
  ,modSrcs
  ,modDeps
  ,modKeys
  ,EnvSlice
  ,mkEnvSlice
  ,Env
  ,emptyEnv
  ,envSetLocal
  ,envSetLocal'
  ,envSetLocal''
  ,envAddLocal
  ,envAddLocal'
  ,envGetLocal
  ,envSetGlobal
  ,mem
  ,showDynamic
  ,unDyn
  ,isBool
  ,isInt
  ,isDouble
  ,isString
  ,isDice
  ,stringType
  ,intType
  ,Dice(Dice)
  ,dices
  ,modifier) where

import Data.Dynamic
import Data.IORef
import Data.List
import qualified Data.Vector as V
import qualified Data.Sequence as S

import Stats(Path)

--type EnvSlice = V.Vector Op
type EnvSlice = Stack

mkEnvSlice :: [Op] -> EnvSlice
mkEnvSlice = lFromList

type EnvGlobal = V.Vector Op
data Env = Env {global :: !EnvGlobal, local :: !EnvSlice} deriving (Show)
emptyEnv = Env {global = V.empty, local = emptyStack}

envSetLocal :: [Op] -> Env -> Env
envSetLocal ops env = env {local = stackFromList ops}

envSetLocal' :: EnvSlice -> Env -> Env
envSetLocal' ops env = env {local = ops}

envSetLocal'' :: [Op] -> EnvSlice -> Env -> Env
envSetLocal'' l s env = env {local = stackAppend (stackFromList l) s}

envSetGlobal :: [Op] -> Env -> Env
envSetGlobal ops env = env {global = gFromList ops}

envAddLocal :: [Op] -> Env -> Env
envAddLocal ops env = env {local = stackAddList ops (local env)}

envAddLocal' :: EnvSlice -> Env -> Env
envAddLocal' ops env = env {local = local env `stackAppend` ops}

envGetLocal :: Env -> EnvSlice
envGetLocal !env = local env

{- EnvSlice needs fast:
  - index
  - concat
-}
data Chunk = 
  Chunk ![Op] !Int
  | Chunk1 !Op 
  | Chunk2 !Op !Op deriving (Show)
chunkLength (Chunk _ l) = l
chunkLength (Chunk1 _) = 1
chunkLength (Chunk2 _ _) = 2
chunkIndex (Chunk d _) i = d !! i
chunkIndex (Chunk1 op) _ = op
chunkIndex (Chunk2 a b) i = if i==0 then a else b
chunkFromList [op] = Chunk1 op
chunkFromList [a, b] = Chunk2 a b
chunkFromList l = Chunk l (length l)

--type Chunk = S.Seq Op
--chunkLength = S.length
--chunkIndex = S.index
--chunkFromList = S.fromList

data StackChunk = StackChunk {chunkStart :: !Int, chunkData :: !Chunk} deriving (Show)
type Stack = [StackChunk]

emptyStack = []
stackSize [] = 0
stackSize (StackChunk {chunkStart = s, chunkData = d} : _) = s + chunkLength d
stackAddList l s = StackChunk {chunkStart = stackSize s, chunkData = chunkFromList l} : s
stackIndex (StackChunk {chunkStart = s, chunkData = d} : scs) i =
  if i >= s then d `chunkIndex` (i - s) else stackIndex scs i
stackAppend s s' = map (\sc -> sc {chunkStart = chunkStart sc + stackSize s}) s' ++ s
stackFromList l = [StackChunk {chunkStart = 0, chunkData = chunkFromList l}]

gIndex = V.unsafeIndex
lIndex = stackIndex
gConcat = (V.++)
lConcat = stackAppend
--lAppend = V.snoc
gFromList = V.fromList
lFromList = stackFromList

mem :: Env -> Int -> Op
mem !env !i = if isGlobal i then g else l
  where
    --g = if (i - 1) > (V.length (global env)) then error $ "no " ++ show (i - 1) ++ " in " ++ show (global env) else global env `gIndex` (i - 1)
    g = global env `gIndex` (i - 1)
    lenv = {-# SCC "tiger:mem:local" #-} local env 
    l = {-# SCC "tiger:mem:local_index" #-} lenv `lIndex` (-i)

isGlobal :: Int -> Bool
isGlobal = (>0)

data Op =
  App !Op ![Op] -- function application
  | Val !Dynamic -- a constant packed in Dynamic
  | Ref !Int -- reference to a slot
  | Lam ![Int] !Int !Op -- lambda definition, declares external symbols as slots
  | Bin1 String !(Env -> Op -> Op) -- builtin unary function
  | Bin2 String !(Env -> Env -> Op -> Op -> Op) -- builtin binary function
  | Bin3 String !(Env -> Env -> Env -> Op -> Op -> Op -> Op) -- builtin ternary function
  | Hash {entries :: [(String, Op)], labels :: [String]} -- a map data structure
  | List [Op] -- a list data structure
  | Let ![Op] !Op -- non-recursive let binding
  | LetRec ![Op] !Op -- recursive let binding
  | Mod {modRoot :: String, modSrcs :: [String], modDeps :: [Path], modKeys :: [Path], modEx :: Op} -- stat mod
  -- runtime only
  | Clr !EnvSlice !Int !Op -- a closure of a lambda
  | Cap !EnvSlice !Op -- a closure of an expression
  | Cell !(IORef Op) -- wraps an expression to allow results of lazy evaluation

data Dice = Dice {dices :: [Int], modifier :: Int} deriving (Typeable)
instance Show Dice where
  show (Dice ds m) = intercalate " + " (map f ds) ++ m'
    where
      m' = if m == 0 then "" else if m > 0 then " +" ++ show m else " -" ++ show (abs m)
      f i = "d" ++ show i

instance Show Op where
  show (App a bs) = "(App " ++ show a ++ " " ++ show bs ++ ")"
  show (Val d) = "(Val " ++ showDynamic d ++ ")"
  show (Lam exts n x) = "(Lam " ++ show exts ++ " " ++ " " ++ show n ++ " " ++ show x ++ ")"
  show (Ref i) = "(Ref " ++ show i ++ ")"
  show (Clr exts n x) = "(Clr " ++ show exts ++ " " ++ show n ++ " " ++ show x ++ ")"
  show (Cap exts x) = "(Cap " ++ show exts ++ " " ++ show x ++ ")"
  show (Bin1 s _) = "(Bin1 " ++ s ++ ")"
  show (Bin2 s _) = "(Bin2 " ++ s ++ ")"
  show (Bin3 s _) = "(Bin3 " ++ s ++ ")"
  show c@(Cell _) = "(Cell ?)"
  show (Hash kvs ls) = "(Hash " ++ show kvs ++ " " ++ show ls ++ ")"
  show (List l) = "(List " ++ show l ++ ")"
  show (Let bs x) = "(Let " ++ show bs ++ show x ++ ")"
  show (LetRec bs x) = "(LetRec " ++ show bs ++ show x ++ ")"
  show (Mod r srcs deps keys x) = 
    "(Mod " ++ show r ++ " " ++ show srcs ++ " " ++ show deps ++ " " ++ show keys ++ " " ++ show x ++ ")"

showDynamic :: Dynamic -> String
showDynamic d | dynTypeRep d == stringType = (fromDyn d "?")
showDynamic d | dynTypeRep d == typeOf (error "" :: Int) = show (fromDyn d 0 :: Int)
showDynamic d | dynTypeRep d == typeOf (error "" :: Integer) = show (fromDyn d 0 :: Integer)
showDynamic d | dynTypeRep d == typeOf (error "" :: Double) = show (fromDyn d 0 :: Double)
showDynamic d | dynTypeRep d == typeOf (error "" :: Bool) = show (fromDyn d True)
showDynamic d | isDice d = show (unDyn d :: Dice)
showDynamic d = "?" ++ show (dynTypeRep d)

stringType = typeOf (error "" :: String)
intType = typeOf (error "" :: Int)
boolType = typeOf (error "" :: Bool)
doubleType = typeOf (error "" :: Double)
diceType = typeOf (error "" :: Dice)

isString = (stringType ==) . dynTypeRep
isInt = (intType ==) . dynTypeRep
isBool = (boolType ==) . dynTypeRep
isDouble = (doubleType ==) . dynTypeRep
isDice = (diceType ==) . dynTypeRep


unDyn :: (Typeable a) => Dynamic -> a
unDyn d = let !a = fromDyn d (error $ "dynCast") in a
