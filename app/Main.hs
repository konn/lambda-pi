module Main (main) where

import Control.Monad (forever)
import Data.Text (Text)
import qualified Data.Text.IO as T
import Language.Lambda.Syntax.LambdaPi (Type, Value, tryEval)
import Language.Lambda.Syntax.LambdaPi.Parser
import System.IO (hFlush, hPutStrLn, stderr, stdout)

main :: IO ()
main = forever $ do
  putStr ">>> "
  hFlush stdout
  src <- T.getLine
  either reportError (printResult src) $
    tryEval =<< parseOnly lambdaExp src

printResult :: Text -> (Value, Type) -> IO ()
printResult inp (val, ty) = do
  T.putStrLn inp
  putStr "\t= "
  print val
  putStr "\t: "
  print ty

reportError :: String -> IO ()
reportError err = do
  hPutStrLn stderr "Compile error:\n"
  hPutStrLn stderr err
