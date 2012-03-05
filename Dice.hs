{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Dice where

import Data.List

class Dice a where
  maxRoll :: a -> Int

class Dice d => Roll a d where
  dice :: Dice d => a -> d
  rolled :: a -> Int

instance Dice Int where
  maxRoll = id

instance Dice d => Roll (Int, d) d where
  dice = snd
  rolled = fst

gen :: [Int] -> [[Int]]
gen [] = [[]]
gen (d:ds) = [i:is | i <- [1..d], is <- gen ds]

tabCount :: (Ord a, Eq a) => [a] -> [(a, Int)]
tabCount = map (\(a:as) -> (a, length as + 1)) . group . sort

prob :: (a -> Bool) -> [a] -> Double
prob f as = fromIntegral i / l
  where (i, l) = foldl (\(i, l) a -> (if f a then i+1 else i, l+1)) (0, 0) as

probs :: [(a, Int)] -> [(a, Double)]
probs as = [(a, fromIntegral i / fromIntegral l) | (a, i) <- as]
  where l = foldl (\a (_, b) -> a + b) 0 as

avg :: [Double] -> Double
avg = (\(x, l) -> x/l) . foldl (\(x, l) a -> (x+a, l+1)) (0.0, 0)

takeTop :: Ord a => Int -> [a] -> [a]
takeTop n = take n . reverse . sort

hitProb ab ac = prob (>=ac) $ map ((+ab) . sum) $ gen [20]
