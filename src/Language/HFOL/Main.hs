module Main where

import Language.TPTP.Pretty
import Language.HFOL.Parser
import Language.HFOL.Latex
import Language.HFOL.ToTPTP
import Language.HFOL.Core
import Language.HFOL.Pretty
import qualified Language.TPTP as T

import Control.Monad

import System.Environment

main :: IO ()
main = do
  file:rest <- getArgs
  ds <- parseFile file
  let (formulas,debug) = toTPTP ds
  -- Verbose output
  when ("-v" `elem` rest)    (mapM_ putStrLn debug)
  -- Supress ordinary output
  when ("-s" `notElem` rest) (putStrLn (prettyTPTP (concatMap snd formulas)))
  -- Latex output
  when ("-l" `elem` rest)  $ do putStrLn (latexHeader file)
                                (mapM_ (putStr . uncurry latexDecl) formulas)
                                putStrLn latexFooter

latexHeader :: String -> String
latexHeader file = unlines
  ["\\documentclass{article}"
  ,"\\usepackage[a4paper]{geometry}"
  ,"\\usepackage{amsmath}"
  ,"\\begin{document}"
  ,"\\title{" ++ file ++ "}"
  ,"\\maketitle"
  ]

latexDecl :: Decl -> [T.Decl] -> String
latexDecl Data            fs = unlines $
  ["\\section{Datatypes}"
  ,"\\begin{align*}"
  ]
  ++ map runLatex fs ++
  ["\\end{align*}"
  ,"\\newpage"
  ]
latexDecl d@(Func fn _ _) fs = unlines $
  ["\\section{" ++ fn ++ "}"
  ,""
  ,"\\subsection{Definition}"
  ,""
  ,"\\begin{verbatim}"
  ,prettyCore d
  ,"\\end{verbatim}"
  ,""
  ,"\\subsection{Axioms}"
  ,""
  ,"\\begin{align*}"
  ]
  ++ map runLatex fs ++
  ["\\end{align*}"
  ,"\\newpage"
  ]

latexFooter :: String
latexFooter = "\\end{document}"