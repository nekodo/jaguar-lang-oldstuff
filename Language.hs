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

def = emptyDef{ commentStart = "{-"
              , commentEnd = "-}"
              , identStart = letter
              , identLetter = alphaNum
              , opStart = oneOf "-+!&|=><\\"
              , opLetter = oneOf "-+!&|=><\\"
              , reservedOpNames = ["+", "-", "!", "&&", "||", "=", "->", "\\", "<", ">"]
              , reservedNames = ["true", "false", "let", "in",
                                 "if", "then", "else"]
              }

TokenParser{ parens = m_parens
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , semiSep1 = m_semiSep1
           , whiteSpace = m_whiteSpace
           , stringLiteral = m_stringLiteral
           , natural = m_natural
           , symbol = m_symbol} = makeTokenParser def

m_integer :: Parser Integer
m_integer = (char '-' >> fmap (0-) m_natural) <|> m_natural

exprparser :: Parser Expr
exprparser = buildExpressionParser table term <?> "expression"
table =
  [[Prefix (m_reservedOp "!" >> return (\x -> Apply (Var $ PathCons "!" PathNil) x))]
  ,[ifix "<", ifix ">"]
  ,[ifix "&&", ifix "||"]
  ,[ifix "+", ifix "-"]]
  where
    ifix op = Infix (m_reservedOp op >>
                       return (\x y -> Apply (Apply (Var $ PathCons op PathNil) x) y)) AssocLeft
term = try appParser
       <|> fmap (Const . toDyn . (fromIntegral :: Integer -> Int)) m_integer
       <|> fmap (Const . toDyn) m_stringLiteral
       <|> (m_reserved "true" >> return (Const $ toDyn True))
       <|> (m_reserved "false" >> return (Const $ toDyn False))
       <|> ifParser
       <|> letParser
       <|> lambdaParser
       <|> listParser
       <|> hashParser

app_start = m_parens exprparser
       <|> fmap Var pathParser

app_arg = m_parens exprparser
       <|> fmap Var pathParser
       <|> fmap (Const . toDyn) intConst
       <|> fmap (Const . toDyn) m_stringLiteral
       <|> (m_reserved "true" >> return (Const $ toDyn True))
       <|> (m_reserved "false" >> return (Const $ toDyn False))
       <|> listParser
       <|> hashParser

intConst :: Parser Int
intConst = fmap (fromIntegral) m_integer

pathparser :: Parser Path
pathparser = do
  fs <- many1 $ try pathfrag
  e <- pathend
  m_whiteSpace
  return $ foldr PathCons e fs

pathend = pathAll <|> return PathNil
pathfrag = char ':' >> many1 alphaNum
pathAll = char ':' >> char '*' >> return PathAll

pathParser = try pathAll <|> pathparser

appParser :: Parser Expr
appParser = do
  f <- app_start
  x <- option f (appArgs f)
  m_whiteSpace
  return x

appArgs f = do
  args <- many $ try app_arg
  return $ foldl Apply f args

ifParser = do
  m_reserved "if"
  c <- exprparser
  m_reserved "then"
  t <- exprparser
  m_reserved "else"
  e <- exprparser
  return $ IfExpr c t e

letParser = do
  m_reserved "let"
  p <- pathParser
  m_reservedOp "="
  x <- exprparser
  m_reserved "in"
  y <- exprparser
  return $ LetExpr p x y

lambdaParser = do
  m_reservedOp "\\"
  p <- pathParser
  m_reservedOp "->"
  e <- exprparser
  return $ Lambda p e

listParser :: Parser Expr
listParser = do
  xs <- between (m_symbol "[") (m_symbol "]") (exprparser `sepBy` m_symbol ",")
  return $ HashMap (zip (map show [0..]) xs)

hashParser :: Parser Expr
hashParser = do
  xs <- between (m_symbol "{") (m_symbol "}") (keyValParser `sepBy` m_symbol ",")
  return $ HashMap xs
  where
    keyValParser = do
      key <- many1 alphaNum
      m_whiteSpace
      m_symbol "="
      val <- exprparser
      return (key, val)

parseExpr :: String -> Either ParseError Expr
parseExpr = parse exprparser ""

parseFile :: String -> IO Expr
parseFile s = do
  defs <- readFile s
  return $ either (error . show) (id) (parseExpr defs)

parseWith p = parse p ""

run :: String -> Expr
run s = runIn s []

runIn :: String -> Env -> Expr
runIn s e = either (error . show) (exprEval (e ++ [(".builtin", HashMap   builtins)])) . parseExpr $ s

loadEnv :: String -> IO Env
loadEnv s = do
  defs <- readFile s
  return $ case run defs of
    HashMap m -> m
    _ -> []
