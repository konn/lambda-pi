{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Rename where

import Control.Lens
import Control.Monad.Trans.Reader
import Data.Generics.Labels ()
import Data.HashMap.Internal.Strict qualified as HM
import Data.HashMap.Strict (HashMap)
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Data.Text (Text)
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow

type RenamedExpr = Expr Rename

type Renamer = Reader RenameEnv

newtype RenameEnv = RenameEnv {boundVars :: HashMap Text Int}
  deriving (Show, Eq, Ord, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid RenameEnv

runRenamer :: Renamer a -> a
runRenamer = flip runReader mempty

renameExpr :: Expr Parse -> Expr Rename
renameExpr = runRenamer . renameExprM

renameExprM :: Expr Parse -> Renamer (Expr Rename)
renameExprM = \case
  Var NoExtField v ->
    view (#boundVars . at v) <&> \case
      Just i -> Var NoExtField $ Local i
      Nothing -> Var NoExtField $ Global v
  Ann NoExtField l r ->
    Ann NoExtField <$> renameExprM l <*> renameExprM r
  Star NoExtField -> pure $ Star NoExtField
  App NoExtField l r ->
    App NoExtField <$> renameExprM l <*> renameExprM r
  Lam NoExtField v mtyp body ->
    Lam NoExtField (Just v)
      <$> mapM renameExprM mtyp
      <*> local (#boundVars %~ HM.insert v 0 . fmap succ) (renameExprM body)
  Pi NoExtField mv typ body ->
    Pi NoExtField (maybeName mv)
      <$> renameExprM typ
      <*> local
        ( #boundVars
            %~ maybe id (`HM.insert` 0) (maybeName mv) . fmap succ
        )
        (renameExprM body)
  Nat NoExtField -> pure $ Nat NoExtField
  Zero NoExtField -> pure $ Zero NoExtField
  Succ NoExtField n -> Succ NoExtField <$> renameExprM n
  NatElim NoExtField t base step n ->
    NatElim NoExtField
      <$> renameExprM t
      <*> renameExprM base
      <*> renameExprM step
      <*> renameExprM n
  Vec NoExtField x n -> Vec NoExtField <$> renameExprM x <*> renameExprM n
  Nil NoExtField x -> Nil NoExtField <$> renameExprM x
  Cons NoExtField t n x xs ->
    Cons NoExtField
      <$> renameExprM t
      <*> renameExprM n
      <*> renameExprM x
      <*> renameExprM xs
  VecElim NoExtField x t base step n xs ->
    VecElim NoExtField
      <$> renameExprM x
      <*> renameExprM t
      <*> renameExprM base
      <*> renameExprM step
      <*> renameExprM n
      <*> renameExprM xs
  Record NoExtField (RecordFieldTypes fs) ->
    Record NoExtField . RecordFieldTypes
      <$> mapM (mapM renameExprM) fs
  MkRecord NoExtField (MkRecordFields fs) ->
    MkRecord NoExtField . MkRecordFields
      <$> mapM (mapM renameExprM) fs
  ProjField NoExtField e t ->
    flip (ProjField NoExtField) t <$> renameExprM e
  XExpr x -> noExtCon x
