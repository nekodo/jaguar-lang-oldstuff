{-# LANGUAGE OverloadedStrings, QuasiQuotes, TypeFamilies, TemplateHaskell, MultiParamTypeClasses #-}
module Jungle where

import Control.Applicative
import Data.List
import Data.Maybe
import Data.Text(Text, unpack)
import Network.HTTP.Base(urlEncode)
import Tiger
import qualified Search as S
import Yesod

data W = W

instance Yesod W

mkYesod "W" [parseRoutes|
/ RootR GET
/search SearchR GET
|]

instance RenderMessage W FormMessage where
    renderMessage _ _ = defaultFormMessage

data DisplayContext = DisplayContext {rootOp :: Op, pathTo :: [String]}
mkSearchPath (DisplayContext {pathTo = p}) = "/" ++ intercalate "/" p
addCtxPath ctx x = ctx {pathTo = pathTo ctx ++ [x]}

mkSearchLink :: DisplayContext -> String -> Widget
mkSearchLink ctx s = toWidget [hamlet| <a href=@{SearchR}?q=#{urlEncode (mkSearchPath ctx)}>#{s}|]

data Displayer = Displayer 
  {displayFull_ :: DisplayContext -> Op -> Widget
  ,displayInline_ :: DisplayContext -> Op -> Widget
  ,matchesOp_ :: DisplayContext -> Op -> Bool}

displayers :: [Displayer]
displayers = 
  [namedDisplayer
  ,listDisplayer
  ,hashDisplayer
  ,opDisplayer]

getDisplayer :: DisplayContext -> Op -> Displayer
getDisplayer ctx op = fromJust $ find (\d -> matchesOp_ d ctx op) displayers

displayFull :: DisplayContext -> Op -> Widget
displayFull ctx op = displayFull_ (getDisplayer ctx op) ctx op

displayInline :: DisplayContext -> Op -> Widget
displayInline ctx op = displayInline_ (getDisplayer ctx op) ctx op

displayResults :: Op -> [S.SResult] -> Widget
displayResults root [r] = displayFull (DisplayContext root (S.path r)) (S.result r)
displayResults root rs = toWidget [whamlet|
  <dl .list>
    $forall r <- rs
      <dt>#{toPath2 r}
      <dd>^{displayInline (DisplayContext root (S.path r)) (S.result r)}
|]

descendTo :: Op -> [String] -> Op
descendTo x [] = x
descendTo (Hash h _) (p:ps) = descendTo (fromJust $ lookup p h) ps
descendTo (List l) (p:ps) = descendTo (l !! read p) ps

getLeaf :: Op -> [String] -> String
getLeaf x p = case descendTo x p of
  Val d -> showDynamic d
  _ -> "?"

hasLabel :: String -> Op -> Bool
hasLabel s (Hash _ ls) = s `elem` ls
hasLabel _ _ = False

opDisplayer = Displayer
  {displayFull_ = \ctx op -> toWidget [hamlet| #{unlines $ prettyPrint 0 op} |]
  ,displayInline_ = \ctx op -> case op of
    Val d -> toWidget [hamlet| #{showDynamic d} |]
    _ -> mkSearchLink ctx "..."
  ,matchesOp_ = \_ _ -> True}

listDisplayer = Displayer
  {displayFull_ = \ctx (List ls) -> let ls' = [0..] `zip` ls in toWidget [whamlet|
    <ol>
      $forall (i, l) <- ls'
        <li>^{displayInline (addCtxPath ctx (show i)) l}
  |]
  ,displayInline_ = \ctx op -> mkSearchLink ctx "[...]"
  ,matchesOp_ = \ctx op -> case op of
    List _ -> True
    _ -> False}

hashDisplayer = Displayer
  {displayFull_ = \ctx (Hash h _) -> toWidget [whamlet|
    <dl>
      $forall (k, v) <- h
        <dt>#{k}
        <dd>^{displayInline (addCtxPath ctx k) v}
  |]
  ,displayInline_ = \ctx op -> mkSearchLink ctx "{...}"
  ,matchesOp_ = \ctx op -> case op of
    Hash _ _ -> True
    _ -> False}

namedDisplayer = Displayer
  {displayFull_ = displayFull_ hashDisplayer
  ,displayInline_ = \ctx op -> mkSearchLink ctx (getLeaf op ["name"])
  ,matchesOp_ = \ctx op -> hasLabel "named" op}

toPath2 r = "/" ++ intercalate "/" (S.path r)
listElemPath ctx i = "/" ++ intercalate "/" (pathTo ctx) ++ "/" ++ show i
hashElemPath ctx k = "/" ++ intercalate "/" (pathTo ctx) ++ "/" ++ k

renderSearch root s = do
  let results = S.runSearch s [root]
  defaultLayout $ do
    setTitle "Jungle"
    addScriptRemote "https://ajax.googleapis.com/ajax/libs/jquery/1.6.2/jquery.min.js"
    toWidget [lucius| 
      h1 { color: green; }
      .hash, .list { padding-left: 1em }
    |]
    toWidget [whamlet| 
      <h1>#{s}
      ^{displayResults root results}
    |]

getRootR :: Handler RepHtml
getRootR = do
  op <- liftIO (loadModule "module.txt")
  renderSearch op "/"

getSearchR :: Handler RepHtml
getSearchR = do
  op <- liftIO (loadModule "module.txt")
  searchString <- runInputGet $ fmap unpack (ireq textField "q")
  let results = S.runSearch searchString [op]
  renderSearch op searchString
