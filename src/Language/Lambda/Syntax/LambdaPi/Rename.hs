{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Lambda.Syntax.LambdaPi.Rename (
  RenamedExpr,
  Renamer,
  RenameEnv,
  renameExpr,
  renameExprM,

  -- * ASTs
  Rename,
) where

import Control.Lens
import Control.Monad.Trans.Reader
import Data.Data (Data)
import Data.Generics.Labels ()
import Data.HashMap.Internal.Strict qualified as HM
import Data.HashMap.Strict (HashMap)
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Data.Text (Text)
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Parser (Parse)

type RenamedExpr = Expr Rename

type Renamer = Reader RenameEnv

newtype RenameEnv = RenameEnv {boundVars :: HashMap Text Int}
  deriving (Show, Eq, Ord, Generic, Data)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid RenameEnv

runRenamer :: Renamer a -> a
runRenamer = flip runReader mempty

renameExpr :: Expr Parse -> Expr Rename
renameExpr = runRenamer . renameExprM

renameExprM :: Expr Parse -> Renamer (Expr Rename)
renameExprM = \case
  Var NoExtField (PrimName _ p) -> pure $ Var NoExtField $ PrimName NoExtField p
  Var NoExtField (Global _ v) ->
    view (#boundVars . at v) <&> \case
      Just i -> Var NoExtField $ Bound NoExtField i
      Nothing -> Var NoExtField $ Global NoExtField v
  Var NoExtField (Bound no _) -> noExtCon no
  Var NoExtField (XName x) -> noExtCon x
  Ann NoExtField l r ->
    Ann NoExtField <$> renameExprM l <*> renameExprM r
  Star NoExtField -> pure $ Star NoExtField
  App NoExtField l r ->
    App NoExtField <$> renameExprM l <*> renameExprM r
  Lam NoExtField v mtyp body ->
    Lam NoExtField (AlphaName v)
      <$> mapM renameExprM mtyp
      <*> abstract v (renameExprM body)
  Pi NoExtField mv typ body ->
    Pi NoExtField (maybe Anonymous AlphaName $ maybeName mv)
      <$> renameExprM typ
      <*> local
        ( #boundVars
            %~ maybe id (`HM.insert` 0) (maybeName mv) . fmap succ
        )
        (renameExprM body)
  Sigma NoExtField mv typ body ->
    Sigma NoExtField (maybe Anonymous AlphaName $ maybeName mv)
      <$> renameExprM typ
      <*> local
        ( #boundVars
            %~ maybe id (`HM.insert` 0) (maybeName mv) . fmap succ
        )
        (renameExprM body)
  Pair NoExtField l r ->
    Pair NoExtField <$> renameExprM l <*> renameExprM r
  Let NoExtField v e body ->
    Let NoExtField (AlphaName v)
      <$> renameExprM e
      <*> abstract v (renameExprM body)
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
  Case NoExtField e (CaseAlts alts) ->
    Case NoExtField
      <$> renameExprM e
      <*> (CaseAlts <$> mapM (mapM renameAlt) alts)
  XExpr x -> noExtCon x

renameAlt :: CaseAlt Parse -> Renamer (CaseAlt Rename)
renameAlt (CaseAlt NoExtField v body) =
  CaseAlt NoExtField (AlphaName v) <$> abstract v (renameExprM body)

abstract :: Text -> Renamer a -> Renamer a
abstract v = local $ #boundVars %~ HM.insert v 0 . fmap succ

data Rename deriving (Show, Eq, Ord, Generic, Data)

type instance XName Rename = NoExtCon

type instance XGlobal Rename = NoExtField

type instance XBound Rename = NoExtField

type instance XPrimName Rename = NoExtField

type instance XName Rename = NoExtCon

type instance XAnn Rename = NoExtField

type instance AnnLHS Rename = Expr Rename

type instance AnnRHS Rename = Expr Rename

type instance XStar Rename = NoExtField

type instance XVar Rename = NoExtField

type instance XApp Rename = NoExtField

type instance AppLHS Rename = Expr Rename

type instance AppRHS Rename = Expr Rename

type instance XLam Rename = NoExtField

type instance LamBindName Rename = AlphaName

type instance LamBindType Rename = Maybe (Expr Rename)

type instance LamBody Rename = Expr Rename

type instance XPi Rename = NoExtField

type instance PiVarName Rename = AlphaName

type instance PiVarType Rename = Expr Rename

type instance PiRHS Rename = Expr Rename

type instance XSigma Rename = NoExtField

type instance SigmaVarName Rename = AlphaName

type instance SigmaVarType Rename = Expr Rename

type instance SigmaBody Rename = Expr Rename

type instance XPair Rename = NoExtField

type instance PairFst Rename = Expr Rename

type instance PairSnd Rename = Expr Rename

type instance XLet Rename = NoExtField

type instance LetName Rename = AlphaName

type instance LetRHS Rename = Expr Rename

type instance LetBody Rename = Expr Rename

type instance XRecord Rename = NoExtField

type instance RecordFieldType Rename = Expr Rename

type instance XProjField Rename = NoExtField

type instance ProjFieldRecord Rename = Expr Rename

type instance XMkRecord Rename = NoExtField

type instance RecordField Rename = Expr Rename

type instance XOpen Rename = NoExtField

type instance OpenRecord Rename = Expr Rename

type instance OpenBody Rename = Expr Rename

type instance XVariant Rename = NoExtField

type instance VariantArgType Rename = Expr Rename

type instance XInj Rename = NoExtField

type instance InjArg Rename = Expr Rename

type instance XCase Rename = NoExtField

type instance CaseArg Rename = Expr Rename

type instance XCaseAlt Rename = NoExtField

type instance CaseAltVarName Rename = AlphaName

type instance CaseAltBody Rename = Expr Rename

type instance XExpr Rename = NoExtCon
