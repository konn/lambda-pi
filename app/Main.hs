module Main where

import Control.Monad (forever)
import qualified Data.Text.IO as T
import Language.Lambda.Syntax.LambdaPi (tryEval)
import Language.Lambda.Syntax.LambdaPi.Parser
import System.IO (hPutStr, hPutStrLn, stderr)

main :: IO ()
main = forever $ do
  src <- T.getLine
  either report print $
    tryEval =<< parseOnly lambdaExp src

report :: String -> IO ()
report err = do
  hPutStrLn stderr "Compile error:\n"
  hPutStrLn stderr err
