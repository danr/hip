{-# LANGUAGE DoRec #-}
module Test.AutoSpec.ParserInternals where

import Control.Applicative
import Data.Parser.Grempa.Grammar
import Data.Parser.Grempa.Dynamic

import qualified Test.AutoSpec.Lexer as L
import Test.AutoSpec.Core

parseString :: String -> [ExtDecl]
parseString = parse parseDynamic . L.lex

parseDynamic :: Parser L.Tok [ExtDecl]
parseDynamic = mkDynamicParser constrWrapper extGrammar

app :: Expr k -> Expr k -> Expr k
app (Cons n es) e  = Cons n (es ++ [e])
app e1          e2 = App e1 e2

extGrammar :: Grammar L.Tok [ExtDecl]
extGrammar = do
  rec
    l <- rule [ L.fromTok <@> L.LIdent "" ]
    u <- rule [ L.fromTok <@> L.UIdent "" ]

    p <- rule [ (NP . PVar) <@> l
              , (NP . (`PCons` [])) <@> u
              , (\x xs -> NP (PCons x xs)) <@ L.LPar <#> u <#> ps <# L.RPar 
              ]
    ps <- several p
    ps0 <- several0 p
    
    d <- rule [ Fun <@> l <#> ps0 <# L.Eq <#> e <# L.Semi ]
    ds <- several d
    
    e  <- rule [ app <@> e <#> e'
               , id  <@> e' ]
    e' <- rule [ Case <@ L.Case <#> l <# L.Of <# L.LBrace <#> brs <# L.RBrace
               , (`Cons` []) <@> u
               , Var <@> l
               , Fail <@ L.Fail
               , id <@ L.LPar <#> e <# L.RPar
               ]

    br <- rule [ (Branch . denest) <@> p <# L.Arrow <#> e ]
    brs <- severalInter L.Semi br

  return ds

