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

data Path = PathCons String Path | PathNil | PathAll deriving (Eq, Ord)

instance Show Path where
  show PathNil = ""
  show PathAll = "*"
  show (PathCons s PathNil) = s
  show (PathCons s p) = s ++ "/" ++ show p

{- contains a b <=> b is within a -}
contains :: Path -> Path -> Bool
contains PathAll _ = True
contains PathNil _ = True
contains (PathCons a as) (PathCons b bs) | a == b = contains as bs
contains _ _ = False

{- either a is within b or b is within a -}
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

class Stat s where
  keys :: s -> [Path]
  deps :: s -> [Path]

-- a-b a-* = true
-- a-* a-b = true
provides :: (Stat s) => Path -> s -> Bool
provides p = any (coincides p) . keys

-- a-b a-* = true
-- a-* a-b = true
dependsOn :: (Stat s) => Path -> s -> Bool
dependsOn p = any (coincides p) . deps

isRootOf :: (Stat s) => Path -> s -> Bool
isRootOf p s = provides p s && not (dependsOn p s)

isModOf :: (Stat s) => Path -> s -> Bool
isModOf p s = provides p s && dependsOn p s

statsAsNodes :: (Stat s) => [s] -> [(s, Int, [Int])]
statsAsNodes stats = map findPreds indexed
  where
	indexed = zip stats [1..]
	findPreds (a, i) = (a, i, [j | (b, j) <- indexed, (i /= j) && isPredOf b a])
	isPredOf b a = any (\p -> if isModOf p a then isRootOf p b else dependsOn p a && provides p b) (deps a)
	
findCycles :: (Stat s) => [s] -> [[s]]
findCycles = catMaybes . map isCycle . stronglyConnComp . statsAsNodes
  where
	isCycle (CyclicSCC stats) = Just stats
	isCycle _ = Nothing

sortForEval :: (Stat s) => [s] -> [s]
sortForEval stats = reverse $ map (\(s, _, _) -> s) $ map lookup $ topSort graph
  where (graph, lookup) = graphFromEdges' $ statsAsNodes stats

{-
evaluate :: [Stat] -> StatTree
evaluate stats = if null cycles then eval [] (sortForEval stats) else error ("cycles: " ++ show cycles)
  where cycles = findCycles stats
	

eval :: StatTree -> [Stat] -> StatTree
eval t [] = t
eval t (s:ss) = eval t' ss
  where	
    depMap = concat $ map (\p -> getImmediateValues p p t) $ deps s
    results = evaluator s depMap
    t' = foldl (\t (p, v) -> insertStat (pinit p) [StatLeaf (plast p) v] t) t results-}
