{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Lambda.Syntax.LambdaPi.Rename where

import Control.Lens
import Control.Monad.Trans.Reader
import Data.Generics.Labels ()
import Data.HashMap.Internal.Strict qualified as HM
import Data.HashMap.Strict (HashMap)
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Data.Text (Text)
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi

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
  Var NoExtField "tt" -> pure $ Var NoExtField $ RnPrim Tt
  Var NoExtField "Unit" -> pure $ Var NoExtField $ RnPrim Unit
  Var NoExtField v ->
    view (#boundVars . at v) <&> \case
      Just i -> Var NoExtField $ RnBound i
      Nothing -> Var NoExtField $ RnGlobal v
  Ann NoExtField l r ->
    Ann NoExtField <$> renameExprM l <*> renameExprM r
  Star NoExtField -> pure $ Star NoExtField
  App NoExtField l r ->
    App NoExtField <$> renameExprM l <*> renameExprM r
  Lam NoExtField v mtyp body ->
    Lam NoExtField (AlphaName v)
      <$> mapM renameExprM mtyp
      <*> local (#boundVars %~ HM.insert v 0 . fmap succ) (renameExprM body)
  Pi NoExtField mv typ body ->
    Pi NoExtField (maybe Anonymous AlphaName $ maybeName mv)
      <$> renameExprM typ
      <*> local
        ( #boundVars
            %~ maybe id (`HM.insert` 0) (maybeName mv) . fmap succ
        )
        (renameExprM body)
  Let NoExtField v e body ->
    Let NoExtField (AlphaName v)
      <$> renameExprM e
      <*> local
        (#boundVars %~ HM.insert v 0 . fmap succ)
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
  Open NoExtField r b ->
    -- FIXME: revisit here after structural subtyping is introduced
    Open NoExtField <$> renameExprM r <*> renameExprM b
  Variant NoExtField (VariantTags vs) ->
    Variant NoExtField . VariantTags <$> mapM (mapM renameExprM) vs
  Inj NoExtField tag p ->
    Inj NoExtField tag <$> renameExprM p
  XExpr x -> noExtCon x
