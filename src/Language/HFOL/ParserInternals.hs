{-# LANGUAGE DoRec #-}
module Language.HFOL.ParserInternals where

import Control.Applicative
import Data.Parser.Grempa.Grammar
import Data.Parser.Grempa.Dynamic

import qualified Language.HFOL.Lexer as L
import Language.HFOL.Core

parseString :: String -> [Decl]
parseString = parse parseDynamic . L.lex

parseDynamic :: Parser L.Tok [Decl]
parseDynamic = mkDynamicParser constrWrapper extGrammar

extGrammar :: Grammar L.Tok [Decl]
extGrammar = do
  rec
    l   <- rule [ L.fromTok <@> L.lident ]
    u   <- rule [ L.fromTok <@> L.uident ]

    ls0 <- several0 l

    d   <- rule [ Func    <@> l <#> ls0 <# L.Eq <#> b <# L.Semi ]
    ds  <- several d

    b   <- rule [ Case    <@  L.Case <#> e <# L.Of <# L.LBrace <#> brs <# L.RBrace
                , Expr    <@> e]

    e   <- rule [ app     <@> e <#> e2
                , id      <@> e2
                ]
    e2  <- rule [ con0    <@> u
                , Var     <@> l
                , id      <@  L.LPar <#> e <# L.RPar ]

    br  <- rule [ (:->)   <@> pd <# L.Arrow <#> e <# L.Semi ]
    brs <- several br

    pd  <- rule [ Default <@  L.Under
                , id      <@> p
                ]
    p   <- rule [ PVar    <@> l
                , PCon    <@> u <#> p2s
                , id      <@  L.LPar <#> p <# L.RPar ]
    p2  <- rule [ PVar    <@> l
                , pcon0   <@> u
                , id      <@  L.LPar <#> p <# L.RPar ]
    p2s <- several0 p2


  return ds

