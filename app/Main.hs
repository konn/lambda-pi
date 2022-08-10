{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}

module Main (main) where

import Data.Generics.Labels ()
import qualified Data.Text.IO as T
import Language.Lambda.Syntax.LambdaPi.REPL
import RIO

data AppEnv = AppEnv {logFun :: LogFunc, envRef :: SomeRef REPLContext}
  deriving (Generic)

instance HasLogFunc AppEnv where
  logFuncL = #logFun
  {-# INLINE logFuncL #-}

instance HasStateRef REPLContext AppEnv where
  stateRefL = #envRef
  {-# INLINE stateRefL #-}

main :: IO ()
main = do
  logOpts <- logOptionsHandle stdout False
  envRef <- newSomeRef mempty
  withLogFunc logOpts $ \logFun ->
    runRIO AppEnv {..} $
      forever $ do
        liftIO $ putStr ">>> " >> hFlush stdout
        liftIO T.getLine >>= readEvalPrintM
