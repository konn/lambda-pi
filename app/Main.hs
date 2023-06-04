{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Lens
import Control.Monad.Loops (whileJust_)
import Data.Generics.Labels ()
import qualified Data.HashMap.Strict as HM
import Data.List (sort)
import qualified Data.Text as T
import Language.Lambda.Syntax.LambdaPi.Parser (keywords)
import Language.Lambda.Syntax.LambdaPi.REPL
import RIO
import RIO.Directory (getHomeDirectory)
import RIO.FilePath ((</>))
import RIO.Orphans ()
import System.Console.Haskeline

data AppEnv = AppEnv {logFun :: LogFunc, envRef :: SomeRef REPLContext}
  deriving (Generic)

instance HasLogFunc AppEnv where
  logFuncL = #logFun
  {-# INLINE logFuncL #-}

instance HasStateRef REPLContext AppEnv where
  stateRefL = #envRef
  {-# INLINE stateRefL #-}

appLineSettings :: RIO AppEnv (Settings (RIO AppEnv))
appLineSettings = do
  home <- getHomeDirectory
  pure
    (defaultSettings @(RIO AppEnv))
      { complete = completeWord Nothing " \n\r\t" $ \inp -> do
          keys <- uses #bindings $ sort . (toList keywords <>) . HM.keys
          let comps =
                [ Completion
                  { replacement = T.unpack candidate
                  , isFinished = True
                  , display = T.unpack candidate
                  }
                | candidate <- keys
                , T.pack inp `T.isPrefixOf` candidate
                ]
          pure comps
      , historyFile = Just $ home </> ".lambda-pi-history"
      }

main :: IO ()
main = do
  logOpts <- logOptionsHandle stdout False
  envRef <- newSomeRef mempty
  withLogFunc logOpts $ \logFun ->
    runRIO AppEnv {..} $ do
      sett <- appLineSettings
      runInputT sett mainLoop `finally` liftIO (putStrLn "Good bye.")
  where
    mainLoop = withInterrupt $ handleInterrupt mainLoop $ do
      whileJust_ (getInputLine ">>> ") $ \inp ->
        handleInterrupt (outputStrLn "^CInterrupted." *> mainLoop) $ do
          lift $ readEvalPrintM $ T.pack inp
