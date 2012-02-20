{-# LANGUAGE DeriveDataTypeable,RecordWildCards #-}
module Hip.Params where

import System.Console.CmdArgs

data Params = Params { files       :: [FilePath]
                     , latex       :: Bool
                     , output      :: Maybe FilePath
                     , warnings    :: Bool
                     , statistics  :: Bool

                     , processes   :: Int
                     , timeout     :: Int
                     , provers     :: String
                     , methods     :: String
                     , reprove     :: Bool
                     , consistency :: Bool

                     , inddepth    :: Int
                     , indvars     :: Int
                     , indhyps     :: Int
                     , indsteps     :: Int

                     , fpimax      :: Int

                     , tptp        :: Bool
                     , core        :: Bool
                     , dbfh        :: Bool
                     , dbfol       :: Bool
                     , dbproof     :: Bool
                     }
  deriving (Show,Data,Typeable)

showParams :: Params -> String
showParams Params{..} = " timeout: " ++ show timeout ++
                        " provers: " ++ provers ++
                        " methods: " ++ methods ++
                        " reprove: " ++ show reprove ++
                        " inddepth: " ++ show inddepth ++
                        " indvars: " ++ show indvars ++
                        " indsteps: " ++ show indsteps ++
                        " fpimax: " ++ show fpimax

defParams :: Params
defParams = Params
  { files       = []      &= args &= typFile
  , latex       = False   &= help "Generate latex output (currently unsupported)"
  , warnings    = False   &= help "Show warnings from translation"
  , output      = Nothing &= opt  "proving/" &= typDir &= help "Output all tptp files in a directory (default proving/)"
  , statistics  = False   &= help "Generate statistics files (run with --reprove)"

  , processes   = 4       &= help "Number of prover processes (default 4)" &= name "p" &= groupname "\nProving settings"
  , timeout     = 1       &= help "Timout of provers in seconds (default 1)" &= name "t"
  , provers     = "evpsx" &= help "Provers to use (e)prover (v)ampire (p)rover9 (s)pass equino(x)"
  , methods     = "pisfa" &= help "Methods to use (p)lain (i)nduction (s)tructural (f)ixpoint (a)pprox"
  , reprove     = False   &= help "Reprove theorems already known to be true"
  , consistency = False   &= help "Try to prove the consistency a file's generated theory"

  , inddepth    = 1       &= help "Max depth to do structural induction (default 1)" &= groupname "\nStructural induction"
  , indvars     = 1       &= help "Number of variables to do structural induction on (default 1)"
  , indhyps     = 200     &= help "Maximum number of hypotheses from structural induction (default 200)"
  , indsteps    = 10      &= help "Maximum number of step cases from structural induction (default 10)"

  , fpimax      = 25      &= help "Maximum number of lifted functions (default 25)" &= groupname "\nFixpoint induction"

  , tptp        = False   &= help "Generate tptp output and terminate" &= name "f"  &= groupname "\nDebug"
  , core        = False   &= help "Translate hs to core and terminate" &= name "c"
  , dbfh        = False   &= help "Print debug output of Haskell -> Core translation"
  , dbfol       = False   &= help "Print debug output of Core -> FOL"
  , dbproof     = False   &= help "Print debug output when making proofs"
  }
  &= summary "autospec v0.1 Dan Rosén danr@student.gu.se"
  &= program "autospec"
  &= verbosity
