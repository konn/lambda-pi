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
{-# LANGUAGE OverloadedStrings #-}
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
  RnId (..),
) where

import Control.Lens
import Control.Monad.Trans.Reader
import Data.Generics.Labels ()
import Data.HashMap.Internal.Strict qualified as HM
import Data.HashMap.Strict (HashMap)
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Data.Text (Text)
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Parser (Parse)
import RIO (tshow)

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
      <*> abstract v (renameExprM body)
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
      <*> abstract v (renameExprM body)
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

data Rename deriving (Show, Eq, Ord, Generic)

type instance XAnn Rename = NoExtField

type instance AnnLHS Rename = Expr Rename

type instance AnnRHS Rename = Expr Rename

type instance XStar Rename = NoExtField

type instance XVar Rename = NoExtField

type instance Id Rename = RnId

data RnId
  = RnGlobal Text
  | RnBound !Int
  | RnPrim Prim
  deriving (Show, Eq, Ord, Generic)

type instance BoundVar Rename = Int

type instance FreeVar Rename = Name

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

type instance XLet Rename = NoExtField

type instance LetName Rename = AlphaName

type instance LetRHS Rename = Expr Rename

type instance LetBody Rename = Expr Rename

type instance XNat Rename = NoExtField

type instance XZero Rename = NoExtField

type instance XSucc Rename = NoExtField

type instance SuccBody Rename = Expr Rename

type instance XNatElim Rename = NoExtField

type instance NatElimRetFamily Rename = Expr Rename

type instance NatElimBaseCase Rename = Expr Rename

type instance NatElimInductionStep Rename = Expr Rename

type instance NatElimInput Rename = Expr Rename

type instance XVec Rename = NoExtField

type instance VecType Rename = Expr Rename

type instance VecLength Rename = Expr Rename

type instance XNil Rename = NoExtField

type instance NilType Rename = Expr Rename

type instance XCons Rename = NoExtField

type instance ConsType Rename = Expr Rename

type instance ConsLength Rename = Expr Rename

type instance ConsHead Rename = Expr Rename

type instance ConsTail Rename = Expr Rename

type instance XVecElim Rename = NoExtField

type instance VecElimEltType Rename = Expr Rename

type instance VecElimRetFamily Rename = Expr Rename

type instance VecElimBaseCase Rename = Expr Rename

type instance VecElimInductiveStep Rename = Expr Rename

type instance VecElimLength Rename = Expr Rename

type instance VecElimInput Rename = Expr Rename

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

instance VarLike RnId where
  varName (RnBound i) = preview $ #boundVars . ix i . _1
  varName (RnGlobal i) = pure $ Just i
  varName (RnPrim p) = pure $ Just $ tshow $ pprint p
