{-# LANGUAGE DoRec #-}
module Language.HFOL.ParserInternals
       (declsGrammar
       ,parseDecls
       ,parseBranch
       ,parsePattern
       ,parseExpr
       )
       where

import Control.Applicative
import Data.Parser.Grempa.Grammar
import Data.Parser.Grempa.Dynamic
import Data.Data

import qualified Language.HFOL.Lexer as L
import Language.HFOL.Core

parseFromGrammar :: Data e => Grammar L.Tok e -> String -> e
parseFromGrammar g = parse (mkDynamicParser constrWrapper g) . L.lex

parseDecls :: String -> [Decl]
parseDecls = parseFromGrammar declsGrammar

parseBranch :: String -> Branch
parseBranch = parseFromGrammar branchGrammar

parsePattern :: String -> Pattern
parsePattern = parseFromGrammar (patternGrammar False)

parseExpr :: String -> Expr
parseExpr = parseFromGrammar exprGrammar

lg :: Grammar L.Tok Name
lg = rule [ L.fromTok <@> L.lident ]

ug :: Grammar L.Tok Name
ug = rule [ L.fromTok <@> L.uident ]

exprGrammar :: Grammar L.Tok Expr
exprGrammar = do
  rec
    l   <- lg
    u   <- ug

    e   <- rule [ app  <@> e <#> e2
                , id   <@> e2
                ]
    e2  <- rule [ con0 <@> u
                , Var  <@> l
                , id   <@  L.LPar <#> e <# L.RPar ]
  return e

patternGrammar :: Bool -> Grammar L.Tok Pattern
patternGrammar parens = do
  rec
    l   <- lg
    u   <- ug

    p   <- rule [ PCon  <@> u <#> p2s
                , id    <@> p2 ]
    p2  <- rule [ PVar  <@> l
                , pcon0 <@> u
                , PWild <@  L.Under
                , id    <@  L.LPar <#> p <# L.RPar ]
    p2s <- several p2

  if parens then return p2
            else return p

branchGrammar :: Grammar L.Tok Branch
branchGrammar = do
  let (-->) :: Pattern -> (Maybe Expr,Expr) -> Branch
      p --> (Just g ,e) = Guard p g :-> e
      p --> (Nothing,e) = NoGuard p :-> e
  rec
    p   <- patternGrammar False
    e   <- exprGrammar
    g   <- rule [ (,) Nothing <@ L.Arrow <#> e
                , (,) . Just  <@ L.Bar   <#> e <# L.Arrow <#> e ]
    br  <- rule [ (-->) <@> p <#> g ]

  return br


declsGrammar :: Grammar L.Tok [Decl]
declsGrammar = do
  rec
    l   <- lg
    u   <- ug

    pp   <- patternGrammar True
    pps0 <- several0 pp

    num <- rule [ L.getNum <@> L.number ]
    c   <- rule [ (,)  <@> u <#> num ]
    cs  <- several c

    d   <- rule [ func <@> l <#> pps0 <# L.Eq <#> b <# L.Semi
                , Data <@  L.Data <#> cs <# L.Semi ]
    ds  <- several d

    b   <- rule [ Case <@  L.Case <#> e <# L.Of <# L.LBrace <#> brs <# L.RBrace
                , Expr <@> e ]

    e   <- exprGrammar

    br  <- branchGrammar
    brs <- severalInter L.Semi br

  return ds

