module Main where

import Control.Monad (forever)
import qualified Data.Text.IO as T
import Language.Lambda.Syntax.LambdaPi (Type, Value, tryEval)
import Language.Lambda.Syntax.LambdaPi.Parser
import System.IO (hFlush, hPutStrLn, stderr, stdout)

main :: IO ()
main = forever $ do
  putStr ">>> "
  hFlush stdout
  src <- T.getLine
  either report reportResult $
    tryEval =<< parseOnly lambdaExp src

reportResult :: (Value, Type) -> IO ()
reportResult (val, ty) =
  print val >> putStrLn ("\t:: " <> show ty)

report :: String -> IO ()
report err = do
  hPutStrLn stderr "Compile error:\n"
  hPutStrLn stderr err
