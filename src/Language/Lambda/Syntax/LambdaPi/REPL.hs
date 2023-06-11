{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Language.Lambda.Syntax.LambdaPi.REPL where

import Control.Exception (Exception)
import Control.Lens (At (at), use, (.=), (.~), (<<?=))
import Control.Monad (when)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import qualified Data.List.NonEmpty as NE
import Data.Maybe (isJust)
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Parser
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Rename
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Typing
import RIO (Display (display), HasLogFunc, IsString (fromString), MonadIO, MonadReader, MonadThrow (throwM), MonadUnliftIO, NonEmpty, catch, displayShow, logError, logInfo, logWarn)
import RIO.State (MonadState)
import Text.Megaparsec (eof, optional, (<|>))

data Stmt
  = Eval (Expr Parse)
  | Let Text (Expr Parse)
  | Clear (Maybe Text)
  | Assume (NonEmpty (Text, Expr Parse))
  deriving (Show)

newtype REPLContext = REPLCtx {bindings :: HashMap Text (Maybe Value, Type)}
  deriving (Show, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid REPLContext

clearM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Maybe Text ->
  m ()
clearM Nothing = do
  #bindings .= mempty
  logInfo "Cleared environment."
clearM (Just var) = do
  #bindings . at var .= Nothing
  logInfo $ "Cleared the information of " <> display var

letM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Text ->
  Expr Inferable ->
  m ()
letM var inf = do
  (val, ty) <- inferEvalM inf
  mx <- #bindings . at var <<?= (Just val, ty)
  when (isJust mx) $ do
    logWarn $ "Overriding existing binding for `" <> display var <> "'"
  logInfo $ display var <> " : " <> displayShow ty

evalM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Text ->
  Expr Inferable ->
  m ()
evalM src trm = do
  (val, typ) <- inferEvalM trm
  logInfo $ display src
  logInfo $ "  = " <> displayShow val
  logInfo $ "  : " <> displayShow typ

{- evalM src recd@MkRecord {} = do
  ctx <- evalContextM
  _Γ <- typingContextM
  case tryEvalWith _Γ ctx recd of
    Left err -> throwM $ TypeError err
    Right (val, typ) -> do
      logInfo $ display src
      logInfo $ "  = " <> displayShow val
      logInfo $ "  : " <> displayShow typ
evalM src Lam {} = do
  throwM $ CouldNotInfer src
 -}

assumeM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Text ->
  Expr Parse ->
  m ()
assumeM var e = do
  case toCheckable $ renameExpr e of
    Just ty -> do
      tyVal <- checkTypeM ty VStar
      m <- #bindings . at var <<?= (Nothing, tyVal)
      when (isJust m) $
        logWarn $
          "Overriding existing binding for `" <> display var <> "'"
    Nothing -> throwM $ TypeError $ "Could not check: " <> show (pprint e)

checkTypeM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Expr Checkable ->
  Value ->
  m Type
checkTypeM trm ty = do
  gamma <- typingContextM
  either (throwM . TypeError) pure $
    typeCheck 0 gamma trm ty
  evalCtx <- evalContextM
  pure $ eval evalCtx trm

data REPLException
  = ParseError String
  | TypeError String
  | CouldNotInfer (NonEmpty (Expr Parse))
  deriving (Show, Generic)
  deriving anyclass (Exception)

inferEvalM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Expr Inferable ->
  m (Value, Type)
inferEvalM trm = do
  ctx <- typingContextM
  typ <-
    either (throwM . TypeError) pure $ typeInfer 0 ctx trm
  evalCtx <- evalContextM
  let !val = eval evalCtx trm
  pure (val, typ)

typingContextM ::
  MonadState REPLContext m => m Context
typingContextM = HM.mapKeys Global <$> use #bindings

evalContextM ::
  MonadState REPLContext m => m Env
evalContextM =
  use #bindings <&> \dic ->
    mempty & #namedBinds .~ HM.mapMaybe fst dic

stmtP :: Parser Stmt
stmtP = clearP <|> letP <|> assumeP <|> Eval <$> exprP

clearP :: Parser Stmt
clearP =
  Clear
    <$ reserved "clear"
    <*> optional identifier

assumeP :: Parser Stmt
assumeP =
  Assume
    <$ reserved "assume"
    <*> (mapM (mapM (maybe (fail "No annotation") pure)) =<< binders)

letP :: Parser Stmt
letP =
  Let <$ reserved "let" <*> identifier <* symbol "=" <*> exprP

readEvalPrintM ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadUnliftIO m
  ) =>
  Text ->
  m ()
readEvalPrintM inp = do
  case parseNamed "<repl>" (space *> stmtP <* eof) inp of
    Left a -> logError $ display $ T.pack a
    Right stmt ->
      runCommand inp stmt `catch` \case
        ParseError str -> logError $ "Parse error: " <> fromString str
        TypeError str -> logError $ "Type error: " <> fromString str
        CouldNotInfer e ->
          logError $
            "Could not infer the type if input: "
              <> displayShow (NE.toList $ fmap pprint e)

runCommand ::
  ( MonadThrow m
  , MonadState REPLContext m
  , MonadReader env m
  , HasLogFunc env
  , MonadIO m
  ) =>
  Text ->
  Stmt ->
  m ()
runCommand inp (Eval te) =
  case toInferable $ renameExpr te of
    Just e -> evalM inp e
    Nothing -> throwM $ CouldNotInfer $ NE.singleton te
runCommand _ (Let var te) =
  case toInferable $ renameExpr te of
    Just e -> letM var e
    Nothing -> throwM $ CouldNotInfer $ NE.singleton te
runCommand _ (Clear mvar) = clearM mvar
runCommand _ (Assume ass) = mapM_ (uncurry assumeM) ass
