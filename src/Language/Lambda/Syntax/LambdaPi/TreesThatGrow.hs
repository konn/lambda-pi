{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A variant of LambdaPi syntax tree a la "<https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf Trees That Grow>" by S. Najd and S. Peyton-Jones.
module Language.Lambda.Syntax.LambdaPi.TreesThatGrow (
  -- * Phases
  Parse,
  Rename,
  Typing,
  XExprTyping (..),
  TypingMode (..),
  STypingMode (..),
  KnownTypingMode (..),
  Inferable,
  Checkable,

  -- * AST
  Name (..),
  Expr (..),
  XExpr,

  -- ** TTG types
  NoExtField (..),
  NoExtCon (),
  noExtCon,

  -- ** Field and/or Constructor extension

  -- *** Type annotation
  XAnn,
  AnnLHS,
  AnnRHS,

  -- *** Star
  XStar,

  -- *** Variables
  XVar,
  Id,
  Var (..),
  castVar,
  BoundVar,
  FreeVar,

  -- *** Application
  XApp,
  AppLHS,
  AppRHS,

  -- *** Lambda abstraction
  XLam,
  LamBindName,
  LamBindType,
  LamBody,

  -- *** Pi-types
  XPi,
  DepName (..),
  maybeName,
  PiVarName,
  PiVarType,
  PiRHS,

  -- *** Naturals
  XNat,

  -- **** constructors
  XZero,
  XSucc,
  SuccBody,

  -- **** eliminator
  XNatElim,
  NatElimRetFamily,
  NatElimBaseCase,
  NatElimInductionStep,
  NatElimInput,

  -- *** Vectors
  XVec,
  VecType,
  VecLength,

  -- **** Constructors
  XNil,
  NilType,
  XCons,
  ConsType,
  ConsLength,
  ConsHead,
  ConsTail,

  -- **** Elminator
  XVecElim,
  VecElimEltType,
  VecElimRetFamily,
  VecElimBaseCase,
  VecElimInductiveStep,
  VecElimLength,
  VecElimInput,

  -- *** Record
  XRecord,
  RecordFieldTypes (..),
  RecordFieldType,

  -- **** Constructors
  XMkRecord,
  MkRecordFields (..),
  RecordField,

  -- **** Eliminators
  XProjField,
  ProjFieldRecord,

  -- * Pretty-printing
  pprint,
  VarLike (..),
  DocM (..),
  HasBindeeType (..),
) where

import Control.Arrow ((>>>))
import Control.Lens
import Control.Monad (forM_)
import Control.Monad.Reader.Class
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Kind (Type)
import Data.Maybe
import Data.Semigroup.Generic
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic, Rep)
import GHC.Generics.Constraint
import RIO (NFData)
import Text.PrettyPrint.Monadic

instance Pretty e NoExtCon where
  pretty = noExtCon

data Name = Global Text | Local Int | Quote Int
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

data Parse deriving (Show, Eq, Ord, Generic)

data Rename deriving (Show, Eq, Ord, Generic)

data TypingMode = Infer | Check
  deriving (Show, Eq, Ord, Generic)

data STypingMode (m :: TypingMode) where
  SInfer :: STypingMode 'Infer
  SCheck :: STypingMode 'Check

class KnownTypingMode m where
  typingModeVal :: STypingMode m

instance KnownTypingMode 'Infer where
  typingModeVal = SInfer

instance KnownTypingMode 'Check where
  typingModeVal = SCheck

data Typing (typeMode :: TypingMode)
  deriving (Show, Eq, Ord, Generic)

data NoExtField = NoExtField
  deriving (Show, Eq, Ord, Generic)

data NoExtCon
  deriving (Show, Eq, Ord, Generic)

noExtCon :: NoExtCon -> a
noExtCon = \case {}

type Inferable = Typing 'Infer

type Checkable = Typing 'Check

type family XAnn phase

type instance XAnn Parse = NoExtField

type instance XAnn Rename = NoExtField

type instance XAnn Inferable = NoExtField

type instance XAnn Checkable = NoExtCon

type family AnnLHS a

type instance AnnLHS Parse = Expr Parse

type instance AnnLHS Rename = Expr Rename

type instance AnnLHS (Typing m) = Expr Checkable

type family AnnRHS a

type instance AnnRHS Parse = Expr Parse

type instance AnnRHS Rename = Expr Rename

type instance AnnRHS (Typing m) = Expr Checkable

type family XStar p

type instance XStar Parse = NoExtField

type instance XStar Rename = NoExtField

type instance XStar Inferable = NoExtField

type instance XStar Checkable = NoExtCon

type family XVar p

type instance XVar Parse = NoExtField

type instance XVar Rename = NoExtField

type instance XVar Inferable = NoExtField

type instance XVar Checkable = NoExtCon

type family Id p

type instance Id Parse = Text

type instance Id Rename = FreeVar Rename

type instance Id (Typing m) = FreeVar (Typing m)

castVar ::
  (BoundVar p ~ BoundVar p', FreeVar p ~ FreeVar p') =>
  Var p ->
  Var p'
castVar (Bound b) = Bound b
castVar (Free b) = Free b

data Var p
  = Bound (BoundVar p)
  | Free (FreeVar p)
  deriving (Generic)

deriving instance
  (Show (BoundVar p), Show (FreeVar p)) =>
  Show (Var p)

deriving instance
  (Eq (BoundVar p), Eq (FreeVar p)) =>
  Eq (Var p)

deriving instance
  (Ord (BoundVar p), Ord (FreeVar p)) =>
  Ord (Var p)

type family BoundVar p

type instance BoundVar Parse = Text

type instance BoundVar Rename = Int

type instance BoundVar (Typing _) = Int

type family FreeVar p

type instance FreeVar Parse = Text

type instance FreeVar Rename = Name

type instance FreeVar (Typing _) = Name

type family XApp p

type instance XApp Parse = NoExtField

type instance XApp Rename = NoExtField

type instance XApp Inferable = NoExtField

type instance XApp Checkable = NoExtCon

type family AppLHS p

type instance AppLHS Parse = Expr Parse

type instance AppLHS Rename = Expr Rename

type instance AppLHS (Typing _) = Expr Inferable

type family AppRHS p

type instance AppRHS Parse = Expr Parse

type instance AppRHS Rename = Expr Rename

type instance AppRHS (Typing _) = Expr Checkable

type family XLam p

type instance XLam Parse = NoExtField

type instance XLam Rename = NoExtField

type instance XLam (Typing _) = NoExtField

type family LamBindName p

type instance LamBindName Parse = Text

type instance LamBindName Rename = Maybe Text

type instance LamBindName (Typing m) = Maybe Text

type family LamBindType p

type instance LamBindType Parse = Maybe (Expr Parse)

type instance LamBindType Rename = Maybe (Expr Rename)

type instance LamBindType Inferable = Expr Checkable

type instance LamBindType Checkable = Maybe (Expr Checkable)

type family LamBody p

type instance LamBody Parse = Expr Parse

type instance LamBody Rename = Expr Rename

type instance LamBody (Typing m) = Expr (Typing m)

type family XPi p

type instance XPi Parse = NoExtField

type instance XPi Rename = NoExtField

type instance XPi Inferable = NoExtField

type instance XPi Checkable = NoExtCon

type family PiVarName p

maybeName :: DepName -> Maybe Text
maybeName = \case
  Indep -> Nothing
  DepAnon -> Nothing
  DepNamed t -> Just t

data DepName = Indep | DepAnon | DepNamed Text
  deriving (Show, Eq, Ord, Generic)

type instance PiVarName Parse = DepName

type instance PiVarName Rename = Maybe Text

type instance PiVarName (Typing _) = Maybe Text

type family PiVarType p

type instance PiVarType Parse = Expr Parse

type instance PiVarType Rename = Expr Rename

type instance PiVarType (Typing _) = Expr Checkable

type family PiRHS p

type instance PiRHS Parse = Expr Parse

type instance PiRHS Rename = Expr Rename

type instance PiRHS (Typing _) = Expr Checkable

type family XNat p

type instance XNat Parse = NoExtField

type instance XNat Rename = NoExtField

type instance XNat Inferable = NoExtField

type instance XNat Checkable = NoExtCon

type family XZero p

type instance XZero Parse = NoExtField

type instance XZero Rename = NoExtField

type instance XZero Inferable = NoExtField

type instance XZero Checkable = NoExtCon

type family XSucc p

type instance XSucc Parse = NoExtField

type instance XSucc Rename = NoExtField

type instance XSucc Inferable = NoExtField

type instance XSucc Checkable = NoExtCon

type family SuccBody p

type instance SuccBody Parse = Expr Parse

type instance SuccBody Rename = Expr Rename

type instance SuccBody (Typing _) = Expr Checkable

type family XNatElim p

type instance XNatElim Parse = NoExtField

type instance XNatElim Rename = NoExtField

type instance XNatElim Inferable = NoExtField

type instance XNatElim Checkable = NoExtCon

type family NatElimRetFamily a

type instance NatElimRetFamily Parse = Expr Parse

type instance NatElimRetFamily Rename = Expr Rename

type instance NatElimRetFamily (Typing _) = Expr Checkable

type family NatElimBaseCase a

type instance NatElimBaseCase Parse = Expr Parse

type instance NatElimBaseCase Rename = Expr Rename

type instance NatElimBaseCase (Typing _) = Expr Checkable

type family NatElimInductionStep a

type instance NatElimInductionStep Parse = Expr Parse

type instance NatElimInductionStep Rename = Expr Rename

type instance NatElimInductionStep (Typing _) = Expr Checkable

type family NatElimInput a

type instance NatElimInput Parse = Expr Parse

type instance NatElimInput Rename = Expr Rename

type instance NatElimInput (Typing _) = Expr Checkable

type family XVec p

type instance XVec Parse = NoExtField

type instance XVec Rename = NoExtField

type instance XVec Inferable = NoExtField

type instance XVec Checkable = NoExtCon

type family VecType p

type instance VecType Parse = Expr Parse

type instance VecType Rename = Expr Rename

type instance VecType (Typing _) = Expr Checkable

type family VecLength p

type instance VecLength Parse = Expr Parse

type instance VecLength Rename = Expr Rename

type instance VecLength (Typing _) = Expr Checkable

type family XNil p

type instance XNil Parse = NoExtField

type instance XNil Rename = NoExtField

type instance XNil Inferable = NoExtField

type instance XNil Checkable = NoExtCon

type family NilType p

type instance NilType Parse = Expr Parse

type instance NilType Rename = Expr Rename

type instance NilType (Typing _) = Expr Checkable

type family XCons p

type instance XCons Parse = NoExtField

type instance XCons Rename = NoExtField

type instance XCons Inferable = NoExtField

type instance XCons Checkable = NoExtCon

type family ConsType p

type instance ConsType Parse = Expr Parse

type instance ConsType Rename = Expr Rename

type instance ConsType (Typing _) = Expr Checkable

type family ConsLength p

type instance ConsLength Parse = Expr Parse

type instance ConsLength Rename = Expr Rename

type instance ConsLength (Typing _) = Expr Checkable

type family ConsHead p

type instance ConsHead Parse = Expr Parse

type instance ConsHead Rename = Expr Rename

type instance ConsHead (Typing _) = Expr Checkable

type family ConsTail p

type instance ConsTail Parse = Expr Parse

type instance ConsTail Rename = Expr Rename

type instance ConsTail (Typing _) = Expr Checkable

type family XVecElim p

type instance XVecElim Parse = NoExtField

type instance XVecElim Rename = NoExtField

type instance XVecElim Inferable = NoExtField

type instance XVecElim Checkable = NoExtCon

type family VecElimEltType p

type instance VecElimEltType Parse = Expr Parse

type instance VecElimEltType Rename = Expr Rename

type instance VecElimEltType (Typing _) = Expr Checkable

type family VecElimRetFamily p

type instance VecElimRetFamily Parse = Expr Parse

type instance VecElimRetFamily Rename = Expr Rename

type instance VecElimRetFamily (Typing _) = Expr Checkable

type family VecElimBaseCase p

type instance VecElimBaseCase Parse = Expr Parse

type instance VecElimBaseCase Rename = Expr Rename

type instance VecElimBaseCase (Typing _) = Expr Checkable

type family VecElimInductiveStep p

type instance VecElimInductiveStep Parse = Expr Parse

type instance VecElimInductiveStep Rename = Expr Rename

type instance VecElimInductiveStep (Typing _) = Expr Checkable

type family VecElimLength p

type instance VecElimLength Parse = Expr Parse

type instance VecElimLength Rename = Expr Rename

type instance VecElimLength (Typing _) = Expr Checkable

type family VecElimInput p

type instance VecElimInput Parse = Expr Parse

type instance VecElimInput Rename = Expr Rename

type instance VecElimInput (Typing _) = Expr Checkable

type family XRecord p

type instance XRecord Parse = NoExtField

type instance XRecord Rename = NoExtField

type instance XRecord Inferable = NoExtField

type instance XRecord Checkable = NoExtCon

type family RecordFieldType p

type instance RecordFieldType Parse = Expr Parse

type instance RecordFieldType Rename = Expr Rename

type instance RecordFieldType (Typing _) = Expr Checkable

newtype RecordFieldTypes p = RecordFieldTypes {recFieldTypes :: [(Text, RecordFieldType p)]}
  deriving (Generic)

deriving instance
  Show (RecordFieldType p) => Show (RecordFieldTypes p)

deriving instance
  Eq (RecordFieldType p) => Eq (RecordFieldTypes p)

deriving instance
  Ord (RecordFieldType p) => Ord (RecordFieldTypes p)

type family XProjField p

type instance XProjField Parse = NoExtField

type instance XProjField Rename = NoExtField

type instance XProjField Inferable = NoExtField

type instance XProjField Checkable = NoExtCon

type family ProjFieldRecord p

type instance ProjFieldRecord Parse = Expr Parse

type instance ProjFieldRecord Rename = Expr Rename

type instance ProjFieldRecord (Typing _) = Expr Inferable

type family XMkRecord p

type instance XMkRecord Parse = NoExtField

type instance XMkRecord Rename = NoExtField

type instance XMkRecord (Typing _) = NoExtField

type family RecordField p

type instance RecordField Parse = Expr Parse

type instance RecordField Rename = Expr Rename

type instance RecordField (Typing m) = Expr (Typing m)

newtype MkRecordFields p = MkRecordFields {mkRecFields :: [(Text, RecordField p)]}
  deriving (Generic)

deriving instance Show (RecordField p) => Show (MkRecordFields p)

deriving instance Eq (RecordField p) => Eq (MkRecordFields p)

deriving instance Ord (RecordField p) => Ord (MkRecordFields p)

deriving anyclass instance NFData (RecordField p) => NFData (MkRecordFields p)

deriving anyclass instance Hashable (RecordField p) => Hashable (MkRecordFields p)

type family XExpr p

type instance XExpr Parse = NoExtCon

type instance XExpr Rename = NoExtCon

type instance XExpr (Typing m) = XExprTyping m

type XExprTyping :: TypingMode -> Type
data XExprTyping m where
  BVar :: Int -> XExprTyping 'Infer
  Inf :: Expr Inferable -> XExprTyping 'Check

deriving instance Show (XExprTyping m)

deriving instance Eq (XExprTyping m)

deriving instance Ord (XExprTyping m)

data Expr phase
  = Ann (XAnn phase) (AnnLHS phase) (AnnRHS phase)
  | Star (XStar phase)
  | Var (XVar phase) (Id phase)
  | App (XApp phase) (AppLHS phase) (AppRHS phase)
  | Lam (XLam phase) (LamBindName phase) (LamBindType phase) (LamBody phase)
  | Pi (XPi phase) (PiVarName phase) (PiVarType phase) (PiRHS phase)
  | Nat (XNat phase)
  | Zero (XZero phase)
  | Succ (XSucc phase) (SuccBody phase)
  | NatElim
      (XNatElim phase)
      (NatElimRetFamily phase)
      (NatElimBaseCase phase)
      (NatElimInductionStep phase)
      (NatElimInput phase)
  | Vec (XVec phase) (VecType phase) (VecLength phase)
  | Nil (XNil phase) (NilType phase)
  | Cons (XCons phase) (ConsType phase) (ConsLength phase) (ConsHead phase) (ConsTail phase)
  | VecElim
      (XVecElim phase)
      (VecElimEltType phase)
      (VecElimRetFamily phase)
      (VecElimBaseCase phase)
      (VecElimInductiveStep phase)
      (VecElimLength phase)
      (VecElimInput phase)
  | Record (XRecord phase) (RecordFieldTypes phase)
  | MkRecord (XMkRecord phase) (MkRecordFields phase)
  | ProjField (XProjField phase) (ProjFieldRecord phase) Text
  | XExpr (XExpr phase)
  deriving (Generic)

instance GPlated (Expr phase) (Rep (Expr phase)) => Plated (Expr phase) where
  plate = gplate
  {-# INLINE plate #-}

deriving instance FieldC Show (Expr phase) => Show (Expr phase)

deriving instance FieldC Eq (Expr phase) => Eq (Expr phase)

deriving instance FieldC Ord (Expr phase) => Ord (Expr phase)

deriving anyclass instance FieldC Hashable (Expr phase) => Hashable (Expr phase)

data PrettyEnv = PrettyEnv
  { levels :: !(HashMap Text Int)
  , boundVars :: !(Seq (Text, Int))
  }
  deriving (Show, Eq, Ord, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid PrettyEnv

class VarLike v where
  varName :: MonadReader PrettyEnv m => v -> m (Maybe Text)

instance VarLike DepName where
  varName Indep = pure Nothing
  varName DepAnon = pure Nothing
  varName (DepNamed n) = pure $ Just n

instance VarLike Text where
  varName = pure . Just

instance VarLike (Maybe Text) where
  varName = pure

instance VarLike Name where
  varName (Local i) = do
    mtn <- preview $ #boundVars . ix i
    case mtn of
      Just (t, n) -> pure $ Just $ t <> T.pack (show n)
      Nothing -> error $ "Out of bound Local var: " <> show i
  varName (Global t) = pure $ Just t
  varName q@Quote {} = error $ "Could not occur: " <> show q

class HasBindeeType v where
  type BindeeType v
  type BindeeType v = v
  bindeeType :: v -> Maybe (BindeeType v)
  default bindeeType :: BindeeType v ~ v => v -> Maybe (BindeeType v)
  bindeeType = Just

instance HasBindeeType (Expr m)

instance HasBindeeType e => HasBindeeType (Maybe e) where
  type BindeeType (Maybe e) = BindeeType e
  bindeeType = (bindeeType =<<)

instance
  ( Pretty PrettyEnv (AnnLHS phase)
  , Pretty PrettyEnv (AnnRHS phase)
  , VarLike (Id phase)
  , Pretty PrettyEnv (AppLHS phase)
  , Pretty PrettyEnv (AppRHS phase)
  , HasBindeeType (LamBindType phase)
  , VarLike (LamBindName phase)
  , Pretty PrettyEnv (LamBody phase)
  , Pretty PrettyEnv (BindeeType (LamBindType phase))
  , VarLike (PiVarName phase)
  , HasBindeeType (PiVarType phase)
  , Pretty PrettyEnv (BindeeType (PiVarType phase))
  , Pretty PrettyEnv (PiRHS phase)
  , Pretty PrettyEnv (SuccBody phase)
  , Pretty PrettyEnv (NatElimRetFamily phase)
  , Pretty PrettyEnv (NatElimBaseCase phase)
  , Pretty PrettyEnv (NatElimInductionStep phase)
  , Pretty PrettyEnv (NatElimInput phase)
  , Pretty PrettyEnv (VecType phase)
  , Pretty PrettyEnv (VecLength phase)
  , Pretty PrettyEnv (NilType phase)
  , Pretty PrettyEnv (ConsType phase)
  , Pretty PrettyEnv (ConsLength phase)
  , Pretty PrettyEnv (ConsHead phase)
  , Pretty PrettyEnv (ConsTail phase)
  , Pretty PrettyEnv (VecElimEltType phase)
  , Pretty PrettyEnv (VecElimRetFamily phase)
  , Pretty PrettyEnv (VecElimBaseCase phase)
  , Pretty PrettyEnv (VecElimInductiveStep phase)
  , Pretty PrettyEnv (VecElimLength phase)
  , Pretty PrettyEnv (VecElimInput phase)
  , Pretty PrettyEnv (RecordFieldType phase)
  , Pretty PrettyEnv (RecordField phase)
  , Pretty PrettyEnv (ProjFieldRecord phase)
  , Pretty PrettyEnv (XExpr phase)
  ) =>
  Pretty PrettyEnv (Expr phase)
  where
  pretty (Ann _ l r) =
    withPrecParens 10 $
      withPrecedence 11 (pretty l) <+> colon <+> pretty r
  pretty Star {} = char '★'
  pretty (Var _ v) = text . fromMaybe "x" =<< varName v
  pretty (App _ l r) =
    withPrecParens 11 $
      pretty l <+> withPrecedence 12 (pretty r)
  pretty (Lam _ mv mp body) = withPrecParens 4 $ do
    let mArgTy = bindeeType mp
    var <- fromMaybe "x" <$> varName mv
    lvl <- views (#levels . at var) (fromMaybe 0)
    hang
      ( char 'λ'
          <+> appWhen
            (isJust mArgTy)
            parens
            ( text var <+> forM_ mArgTy \ty ->
                colon <+> pretty ty
            )
          <+> char '.'
      )
      2
      $ local
        ( #levels . at var ?~ (lvl + 1)
            >>> #boundVars %~ (Seq.<|) (var, lvl)
        )
        (pretty body)
  pretty (Pi _ mv mp body) = withPrecParens 4 $ do
    -- TODO: check occurrence of mv in body and
    -- use arrows if absent!
    let mArgTy = bindeeType mp
    var <- fromMaybe "x" <$> varName mv
    lvl <- views (#levels . at var) (fromMaybe 0)
    hang
      ( char 'Π'
          <+> appWhen
            (isJust mArgTy)
            parens
            ( text var <+> forM_ mArgTy \ty ->
                colon <+> pretty ty
            )
          <+> char '.'
      )
      2
      $ local
        ( #levels . at var ?~ lvl + 1
            >>> #boundVars %~ (Seq.<|) (var, lvl)
        )
        (pretty body)
  pretty Nat {} = text "ℕ"
  pretty Zero {} = text "0"
  -- FIXME: compress numerals
  pretty (Succ _ e) = withPrecParens 11 $ text "succ" <+> pretty e
  pretty (NatElim _ t b i n) =
    withPrecParens 11 $
      text "natElim" <+> pretty t <+> pretty b <+> pretty i <+> pretty n
  pretty (Vec _ a n) =
    withPrecParens 11 $
      text "Vec" <+> pretty a <+> pretty n
  pretty (Nil _ a) =
    withPrecParens 11 $ text "nil" <+> pretty a
  pretty (Cons _ a n x xs) =
    withPrecParens 11 $
      text "cons"
        <+> pretty a
        <+> pretty n
        <+> pretty x
        <+> pretty xs
  pretty (VecElim _ a t b i n xs) =
    withPrecParens 11 $
      text "vecElim" <+> pretty a <+> pretty t <+> pretty b <+> pretty i <+> pretty n <+> pretty xs
  pretty (Record _ (RecordFieldTypes flds)) =
    braces $
      sep $
        punctuate
          comma
          [ text f <+> colon <+> pretty e
          | (f, e) <- flds
          ]
  pretty (MkRecord _ (MkRecordFields flds)) =
    braces $
      sep $
        punctuate
          comma
          [ text f <+> equals <+> pretty e
          | (f, e) <- flds
          ]
  pretty (ProjField _ e fld) =
    withPrecParens 12 (pretty e <> "#" <> text fld)
  pretty (XExpr e) = pretty e

instance Pretty PrettyEnv (XExprTyping m) where
  pretty (BVar i) = do
    mtn <- preview $ #boundVars . ix i
    case mtn of
      Just (t, n) -> text t <> char '_' <> int n
      Nothing -> error $ "Out of bound Local var: " <> show i
  pretty (Inf e) = pretty e

pprint :: Pretty PrettyEnv a => a -> Doc
pprint = execDocM (mempty @PrettyEnv) . pretty

{-
occurs :: Int -> Expr (Typing m) -> Bool
occurs i (XExpr (Inf te')) = occurs i te'
occurs i (Lam _ _ _ te') = occurs (i + 1) te'
occurs i (MkRecord _ flds) = any (occurs i . snd) flds
occurs i (Ann _ te' te2) = occurs i te' || occurs i te2
occurs _ Star {} = False
occurs i (Pi _ _ te' te2) =
  occurs i te' || occurs (i + 1) te2
occurs i (NatElim _ te' te2 te3 te4) =
  occurs i te' || occurs i te2 || occurs i te3 || occurs i te4
occurs i (Bound n)
  | i == n = True
  | otherwise = False
occurs _ Free {} = False
occurs i (App _ te' te2) = occurs i te' || occurs i te2
occurs _ Nat {} = False
occurs _ Zero {} = False
occurs i (Succ _ te') = occurs i te'
occurs i (Vec _ te' te2) = occurs i te' || occurs i te2
occurs i (Nil _ te') = occurs i te'
occurs i (Cons _ te' te2 te3 te4) = occurs i te' || occurs i te2 || occurs i te3 || occurs i te4
occurs i (VecElim _ te' te2 te3 te4 te5 te6) =
  occurs i te'
    || occurs i te2
    || occurs i te3
    || occurs i te4
    || occurs i te5
    || occurs i te6
occurs i (Record _ (RecordFieldTypes flds)) = any (occurs i . snd) flds
occurs i (ProjField _ e _) = occurs i e
 -}
