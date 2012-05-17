{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

module Dice where

import Data.List

class Dice d where
  minRoll :: d -> Int
  maxRoll :: d -> Int

class Dice d => Roll r d where
  dice :: Dice d => r -> d
  rolled :: r -> Int

instance Dice Int where
  minRoll = const 1
  maxRoll = id

instance Dice d => Roll (Int, d) d where
  dice = snd
  rolled = fst

data IntDice =
  Dice Int
  | Const Int
  deriving (Show)
  
class Diceslike a where
  asIntDices :: a -> [IntDice]
  (&/) :: (Diceslike b) => a -> b -> [IntDice]
  a &/ b = asIntDices a ++ asIntDices b
  (+/) :: a -> Int -> [IntDice]
  a +/ b = a &/ Const b

instance Dice IntDice where
  minRoll (Const x) = x
  minRoll (Dice _) = 1
  maxRoll (Const x) = x
  maxRoll (Dice x) = x

instance Diceslike IntDice where
  asIntDices = (:[])

instance Diceslike [IntDice] where
  asIntDices = id

d = Dice
d2 = d 2
d3 = d 3
d4 = d 4
d6 = d 6
d8 = d 8
d10 = d 10
d12 = d 12
d20 = d 20
c = Const

gen :: (Dice d) => [d] -> [[Int]]
gen [] = [[]]
gen (d:ds) = [i:is | i <- [(minRoll d)..(maxRoll d)], is <- gen ds]

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

hitProb ab ac = prob isHit $ map sum (gen [20 :: Int])
  where
    isHit x = (x /= 1) && ((x == 20) || (x + ab >= ac))

critProb ab ac critMin = prob isThreat (map sum (gen [20 :: Int])) * hitProb ab ac
  where
    isThreat x = (hasHit x) && (x >= critMin)
    hasHit x = (x /= 1) && ((x + ab >= ac) || (x == 20))

data Dmg = Dmg 
  {mult :: [IntDice]
  ,noMult :: [IntDice]
  ,critOnly :: [IntDice]
  ,noCritOnly :: [IntDice]}

emptyDmg = Dmg [] [] [] []
nonCritDmg (Dmg m nm _ nc) = m ++ nm ++ nc
critDmg cm (Dmg m nm c _) = nm ++ c ++ concat (replicate cm m)
(+/+) :: Dmg -> Dmg -> Dmg
(Dmg m nm c nc) +/+ (Dmg m' nm' c' nc') = Dmg (m ++ m') (nm ++ nm') (c ++ c') (nc ++ nc')
constDmg i = emptyDmg {mult = [Const i]}

atkDmgC ab dmg cr cm ac dr = hp * hd + cp * cd
  where
    cp = critProb ab ac cr
    hp = hitProb ab ac - cp
    hd = avg (map (fromIntegral . max 0 . (\x -> x - dr) . sum) (gen $ nonCritDmg dmg))
    cd = avg (map (fromIntegral . max 0 . (\x -> x - dr) . sum) (gen $ critDmg cm dmg))

atksDmgC atks ac dr = sum $ map (\(ab, dmg, cr, cm) -> atkDmgC ab dmg cr cm ac dr) atks

data Atk = Atk
  {attackBonus :: Int
  ,attackDamage :: Dmg
  ,minCritRoll :: Int
  ,critMultiplier :: Int}

atkHitProb ac (Atk {attackBonus = ab}) = hitProb ab ac
atkCritProb ac (Atk {attackBonus = ab, minCritRoll = cr}) = critProb ab ac cr
atkAvgDmg ac dr (Atk ab dmg cr cm) = atkDmgC ab dmg cr cm ac dr
atksAvgDmg ac dr atks = sum (map (atkAvgDmg ac dr) atks)

data Strategy = Strategy
  {strategyName :: String
  ,strategyAttacks :: [Atk]}

runStrategy :: Int -> Int -> Strategy -> (Double, String)
runStrategy ac dr (Strategy n atks) = (atksAvgDmg ac dr atks, n)

testStrategies :: Int -> Int -> [Strategy] -> [(Double, String)]
testStrategies ac dr = reverse . sort . map (runStrategy ac dr)

falchionDmg = emptyDmg {mult = d4 &/ d4}

fauchardAtk ab dmg = Atk ab (emptyDmg {mult = [d10]} +/+ constDmg dmg) 15 2
horsechopperAtk ab dmg = Atk ab (emptyDmg {mult = [d10]} +/+ constDmg dmg) 19 3
bardicheAtk ab dmg = Atk ab (emptyDmg {mult = [d10]} +/+ constDmg dmg) 17 2

raenSgs =
  [Strategy "fauchard" [fauchardAtk ab dmg, fauchardAtk (ab - 5) dmg]
  ,Strategy "p-fauchard" [fauchardAtk pab pdmg, fauchardAtk (pab - 5) pdmg]
  ,Strategy "horsechop" [horsechopperAtk ab dmg, horsechopperAtk (ab - 5) dmg]
  ,Strategy "p-horsechop" [horsechopperAtk (pab+2) pdmg, horsechopperAtk (pab - 5) pdmg]
  ,Strategy "bardiche" [bardicheAtk ab dmg, bardicheAtk (ab - 5) dmg]
  ,Strategy "p-bardiche" [bardicheAtk (pab+2) pdmg, bardicheAtk (pab - 5) pdmg]]
  where
    ab = 6 + 4 + 1 + 1 + 1
    pab = ab - 2
    dmg = 5 + 2 + 1
    pdmg = dmg + 6
