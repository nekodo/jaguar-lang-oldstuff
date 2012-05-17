-----------------------------------------------------------------------------
--
-- Module      :  Language
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

module Language where

import Stats
import Expressions

import Control.Applicative((<*))
import Data.Dynamic
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language

reserved_ = ["true", "false", "let", "in", "if", "then", "else", "import", "def"]

def = emptyDef{ commentStart = "{-"
              , commentEnd = "-}"
              , identStart = letter
              , identLetter = alphaNum
              , opStart = oneOf "-+!&|=><\\"
              , opLetter = oneOf "-+!&|=><\\"
              , reservedOpNames = ["+", "-", "!", "&&", "||", "=", "->", "<-","\\", "<", ">", "*", "/", "++", "=="]
              , reservedNames = reserved_
              }

TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace
           , stringLiteral = m_stringLiteral
           , natural = m_natural
           , float = m_float
           , symbol = m_symbol} = makeTokenParser def

m_integer :: Parser Integer
m_integer = (char '-' >> fmap (0-) m_natural) <|> m_natural

exprparser :: Parser Expr
exprparser = exprparser' False

exprparser' isMod = buildExpressionParser table (term isMod) <?> "expression"
table =
  [[Prefix (m_reservedOp "!" >> return (\x -> Apply (Var $ PathCons "!" PathNil) x))]
  ,[ifix "<", ifix ">"]
  ,[ifix "&&", ifix "||", ifix "=="]
  ,[ifix "+", ifix "-", ifix "++"]
  ,[ifix "*", ifix "/"]]
  where
    ifix op = Infix (m_reservedOp op >>
                       return (\x y -> Apply (Apply (Var $ PathCons op PathNil) x) y)) AssocLeft
term isMod = try (appParser isMod)
       <|> try (fmap (Const . toDyn) m_float)
       <|> fmap (Const . toDyn . (fromIntegral :: Integer -> Int)) m_integer
       <|> fmap (Const . toDyn) m_stringLiteral
       <|> (m_reserved "true" >> return (Const $ toDyn True))
       <|> (m_reserved "false" >> return (Const $ toDyn False))
       <|> ifParser isMod
       <|> letParser isMod
       <|> lambdaParser isMod
       <|> listParser isMod
       <|> hashParser isMod
       <|> labelApp isMod

app_start isMod = m_parens (exprparser' isMod)
       <|> fmap Var (pathParser isMod)

app_arg isMod = m_parens (exprparser' isMod)
       <|> fmap Var (pathParser isMod)
       <|> try (fmap (Const . toDyn) m_float)
       <|> fmap (Const . toDyn) intConst
       <|> fmap (Const . toDyn) m_stringLiteral
       <|> (m_reserved "true" >> return (Const $ toDyn True))
       <|> (m_reserved "false" >> return (Const $ toDyn False))
       <|> listParser isMod
       <|> hashParser isMod

intConst :: Parser Int
intConst = fmap (fromIntegral) m_integer

pathparser :: Bool -> Parser Path
pathparser False = do
  c <- letter
  cs <- many alphaNum
  let s = c:cs
  if s `elem` reserved_
    then fail "reserved!"
    else do
      fs <- many $ try pathfrag
      e <- pathend
      m_whiteSpace
      return $ foldr PathCons e (s:fs)

pathparser True = p <|> pathparser False
  where 
    p = do
      char '@'
      s <- many1 alphaNum
      fs <- many $ try pathfrag
      e <- pathend
      m_whiteSpace
      return $ foldr PathCons e (('@':s):fs)

pathend = pathAll <|> return PathNil
pathfrag = char ':' >> many1 alphaNum
pathAll = char ':' >> char '*' >> return PathAll

pathParser isMod = try pathAll <|> pathparser isMod

appParser :: Bool -> Parser Expr
appParser isMod = do
  f <- app_start isMod
  x <- option f (appArgs isMod f)
  m_whiteSpace
  return x

appArgs isMod f = do
  args <- many $ try (app_arg isMod)
  return $ foldl Apply f args

ifParser isMod = do
  m_reserved "if"
  c <- exprparser' isMod
  m_reserved "then"
  t <- exprparser' isMod
  m_reserved "else"
  e <- exprparser' isMod
  return $ IfExpr c t e

letParser isMod = do
  m_reserved "let"
  p <- pathParser False
  m_reservedOp "="
  x <- exprparser' isMod
  m_reserved "in"
  y <- exprparser' isMod
  return $ LetExpr p x y

lambdaParser isMod = do
  m_reservedOp "\\"
  ps <- many1 (pathParser False)
  m_reservedOp "->"
  e <- exprparser' isMod
  return $ foldr Lambda e ps

listParser :: Bool -> Parser Expr
listParser isMod = do
  xs <- between (m_symbol "[") (m_symbol "]") (exprparser' isMod `sepBy` m_symbol ",")
  return $ ListExpr xs

--labelParser :: Parser [String]
labelParser c = (char c >> many1 alphaNum >>= (\s -> m_whiteSpace >> return s))

labelApp isMod = do
  l <- labelParser '#'
  e <- exprparser' isMod
  return $ Apply (Apply (Var (PathCons "addLabel" PathNil)) (Const $ toDyn l)) e

hashParser :: Bool -> Parser Expr
hashParser isMod = do
  xs <- between (m_symbol "{") (m_symbol "}") ((modListParser <|> keyValParser) `sepBy` m_symbol ",")
  return $ HashMap xs []
  where
    keyValParser = do
      key <- many1 alphaNum
      m_whiteSpace
      m_symbol "="
      val <- exprparser' isMod
      return (key, val)

modListParser = do
  l <- labelParser '#'
  xs <- between (m_symbol "{") (m_symbol "}") (modParser `sepBy` m_symbol ",")
  return $ ('#':l, ModList l xs)

modParser = do
  p <- pathParser False
  m_reservedOp "<-"
  val <- modExpr
  return (p, val)

modExpr = exprparser' True

defParser = do
  m_reserved "def"
  n <- m_identifier
  m_symbol "="
  e <- exprparser
  return (n, e)

importParser = do
  m_reserved "import"
  s <- m_stringLiteral
  return s

moduleParser = do
  is <- many importParser
  ds <- many1 defParser
  return $ Module is ds

parseExpr :: String -> Either ParseError Expr
parseExpr = parse exprparser ""

parseFile :: String -> IO Expr
parseFile s = do
  defs <- readFile s
  return $ either (error . show) (id) (parseExpr defs)

parseModule :: String -> IO Module
parseModule s = do
  defs <- readFile s
  return $ either (error . show) (id) (parseWith moduleParser defs)

parseWith p = parse p ""
