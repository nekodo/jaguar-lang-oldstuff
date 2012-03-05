{-# LANGUAGE TypeSynonymInstances #-}
-----------------------------------------------------------------------------
--
-- Module      :  Stats
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Stats where

import Control.Monad
import Data.Dynamic
import Data.Graph
import Data.List
import Data.Maybe
import GHC.Exts

data StatNode = StatLeaf String Dynamic | StatBranch String [StatNode]
type StatTree = [StatNode]

instance Show StatNode where
  show (StatLeaf k v) = "(" ++ k ++ " = " ++ showDynamic v ++ ")"
  show (StatBranch k t) = "(" ++ k ++ " = " ++ show t ++ ")"

showDynamic :: Dynamic -> String
showDynamic d | dynTypeRep d == typeOf (error "" :: String) = (fromDyn d "?")
showDynamic d | dynTypeRep d == typeOf (error "" :: Int) = show (fromDyn d 0 :: Int)
showDynamic d | dynTypeRep d == typeOf (error "" :: Integer) = show (fromDyn d 0 :: Integer)
showDynamic d | dynTypeRep d == typeOf (error "" :: Bool) = show (fromDyn d True)
showDynamic _ = "?"

data Path = PathCons String Path | PathNil | PathAll deriving (Eq, Ord)

instance Show Path where
  show PathNil = ""
  show PathAll = "*"
  show (PathCons s PathNil) = s
  show (PathCons s p) = s ++ "/" ++ show p

contains :: Path -> Path -> Bool
contains PathAll _ = True
contains PathNil PathNil = True
contains (PathCons a as) (PathCons b bs) | a == b = contains as bs
contains _ _= False

coincides :: Path -> Path -> Bool
coincides a b = contains a b || contains b a

pinit :: Path -> Path
pinit (PathCons _ PathNil) = PathNil
pinit (PathCons n p) = PathCons n (pinit p)

plast :: Path -> String
plast (PathCons n PathNil) = n
plast (PathCons _ p) = plast p

pappend :: String -> Path -> Path
pappend n PathNil = PathCons n PathNil
pappend n PathAll = PathCons n PathNil
pappend n (PathCons m p) = PathCons m (pappend n p)

label (StatLeaf l _) = l
label (StatBranch l _) = l

insertStat :: Path -> StatTree -> StatTree -> StatTree
insertStat PathNil a b = applyUpdates a b
  where
    applyUpdates [] b = b
    applyUpdates (a:as) b = applyUpdates as (update a b)
    update a [] = [a]
    update a (b:bs) | label a == label b = a:bs
    update a (b:bs) = b : update a bs
insertStat (PathCons k ks) a [] = [StatBranch k (insertStat ks a [])]
insertStat (PathCons k ks) a (StatBranch n cs : bs) | k==n = StatBranch k (insertStat ks a cs) : bs
insertStat ks a (b:bs) = b : (insertStat ks a bs)

getStat :: Path -> StatTree -> Maybe Dynamic
getStat (PathCons k PathNil) ns = case (find ((k==) . label) ns) of
  Just (StatLeaf _ v) -> Just v
  _ -> Nothing
getStat (PathCons k p) ns = case (find ((k==) . label) ns) of
  Just (StatBranch _ ms) -> getStat p ms
  _ -> Nothing
getStat _ _ = Nothing

getImmediateValues :: Path -> Path -> StatTree -> [(Path, Dynamic)]
getImmediateValues p PathAll ns = catMaybes . map f $ ns
  where
    f (StatLeaf k v) = Just (pappend k p, v)
    f _ = Nothing
getImmediateValues p (PathCons k PathNil) ns = case (find ((k==) . label) ns) of
  Just (StatLeaf _ v) -> [(p, v)]
  _ -> []
getImmediateValues p (PathCons k ks) ns = case (find ((k==) . label) ns) of
  Just (StatBranch _ ms) -> getImmediateValues p ks ms
  _ -> []
getImmediateValues _ _ _ = []

data Stat = Stat
  {keys :: [Path]
  ,deps :: [Path]
  ,evaluator :: [(Path, Dynamic)] -> [(Path, Dynamic)]}

dummyStat d k s = Stat {keys= k, deps = d, evaluator = eval}
  where
    get m k = join (fmap fromDynamic (lookup k m)) :: Maybe String
    eval m = zip k (repeat v)
      where v = toDyn $ foldl (++) s (map (fromMaybe "?" . get m) d)

dummyStats =
  [dummyStat [b, c] [c] "0"
  ,dummyStat [] [a] "1"
  ,dummyStat [a, b] [c] "2"
  ,dummyStat [a] [b] "3"
  ,dummyStat [a] [a] "4"
  ,Stat {deps = [PathAll], keys = [count], evaluator = (\m -> [(count, toDyn $ length m)])}]
  where
	a = PathCons "a" PathNil
	b = PathCons "b" PathNil
	c = PathCons "c" PathNil
	count = PathCons "count" PathNil

instance Show Stat where
  show s = show (deps s) ++ " -> " ++ show (keys s)

-- a-b a-* = true
-- a-* a-b = true
provides :: Path -> Stat -> Bool
provides p = any (coincides p) . keys

-- a-b a-* = true
-- a-* a-b = true
dependsOn :: Path -> Stat -> Bool
dependsOn p = any (coincides p) . deps

isRootOf :: Path -> Stat -> Bool
isRootOf p s = provides p s && not (dependsOn p s)

isModOf :: Path -> Stat -> Bool
isModOf p s = provides p s && dependsOn p s

statsAsNodes :: [Stat] -> [(Stat, Int, [Int])]
statsAsNodes stats = map findPreds indexed
  where
	indexed = zip stats [1..]
	findPreds (a, i) = (a, i, [j | (b, j) <- indexed, (i /= j) && isPredOf b a])
	isPredOf b a = any (\p -> if isModOf p a then isRootOf p b else dependsOn p a && provides p b) (deps a)
	
findCycles :: [Stat] -> [[Stat]]
findCycles = catMaybes . map isCycle . stronglyConnComp . statsAsNodes
  where
	isCycle (CyclicSCC stats) = Just stats
	isCycle _ = Nothing

sortForEval :: [Stat] -> [Stat]
sortForEval stats = reverse $ map (\(s, _, _) -> s) $ map lookup $ topSort graph
  where (graph, lookup) = graphFromEdges' $ statsAsNodes stats

evaluate :: [Stat] -> StatTree
evaluate stats = if null cycles then eval [] (sortForEval stats) else error ("cycles: " ++ show cycles)
  where cycles = findCycles stats
	

eval :: StatTree -> [Stat] -> StatTree
eval t [] = t
eval t (s:ss) = eval t' ss
  where	
    depMap = concat $ map (\p -> getImmediateValues p p t) $ deps s
    results = evaluator s depMap
    t' = foldl (\t (p, v) -> insertStat (pinit p) [StatLeaf (plast p) v] t) t results
