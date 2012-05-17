{-# LANGUAGE MultiParamTypeClasses, TypeFamilies #-}

module Search where

import Control.Monad
import Data.List
import Tiger(Op(Val,Hash,List), showDynamic)
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr

class Searchable a where
  asOp :: a -> Op
  asResult :: a -> SResult
  getChildren :: String -> a -> [SResult]
  getDescendants :: a -> [SResult]
  getDescendants a = let cs = getChildren [] a in cs ++ concatMap getDescendants cs
  getLabels :: a -> [String]
  getContent :: a -> String
  
data SResult = SResult {path :: [String], result :: Op} deriving (Show)
prependPath a s@(SResult {path = b}) = s {path = a ++ b}

instance Searchable Op where
  asOp = id
  asResult = SResult []
  getChildren prefix (Hash h _) = map (\(k, v) -> SResult [k] v) $ filter (isPrefixOf prefix .fst) $ h
  getChildren prefix (List l) = map (\(k, v) -> SResult [k] v) $ filter (isPrefixOf prefix . fst) $ (map show [0..]) `zip` l
  getChildren _ _ = []
  getLabels (Hash _ ls) = ls
  getLabels _ = []
  getContent (Val d) = showDynamic d
  getContent _ = ""

instance Searchable SResult where
  asOp = result
  asResult = id
  getChildren p r = map (prependPath (path r)) (getChildren p (result r))
  getDescendants r = map (prependPath (path r)) (getDescendants (result r))
  getLabels = getLabels . result
  getContent = getContent . result

data SOp =
  SChildren String
  | SDescendants
  | SLabel String
  | SContent String
  | SFilterS [SOp]
  | SFilterF Op 
  deriving (Show)

search :: (Searchable a) => [SOp] -> [a] -> [SResult]
search s = concatMap (searchOne s)

searchOne :: (Searchable a) => [SOp] -> a -> [SResult]
searchOne [] a = [asResult a]
searchOne (s:ss) a = search ss (applySOp s a)

applySOp :: (Searchable a) => SOp -> a -> [SResult]
applySOp (SChildren prefix) = getChildren prefix
applySOp SDescendants = getDescendants
applySOp (SLabel label) = filterS (elem label . getLabels)
applySOp (SContent content) = filterS (isInfixOf content . getContent)
applySOp (SFilterS s) = filterS (not . null . searchOne s)
applySOp (SFilterF op) = error "not yet implemented"

filterS :: (Searchable a) => (Op -> Bool) -> a -> [SResult]
filterS f a = if f (asOp a) then [asResult a] else []

sChildrenP, sDescendantsP, sLabelP, sContentP, sFilterSP, sOpP :: Parser SOp
sChildrenP = char '/' >> many alphaNum >>= return . SChildren
sDescendantsP = char '*' >> return SDescendants
sLabelP = char '@' >> many alphaNum >>= return . SLabel
sContentP = between (char '[') (char ']') (many1 (noneOf "]")) >>= return . SContent
sFilterSP = between (char '(') (char ')') searchP >>= return . SFilterS
sOpP = sChildrenP <|> sDescendantsP <|> sLabelP <|> sContentP <|> sFilterSP

searchP :: Parser [SOp]
searchP = many1 sOpP

parseWith p = parse p ""

runSearch :: (Searchable a) => String -> [a] -> [SResult]
runSearch s = search (either (error . show) id (parseWith searchP s))
