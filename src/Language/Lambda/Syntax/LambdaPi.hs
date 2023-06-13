{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{- |
Implementation based on:
"<https://www.andres-loeh.de/LambdaPi/ A Tutorial Implementation of a Dependently Typed Lambda Calculus>"
by Andres Löh, Conor McBride, and Wouter Swiestra.
This is a variant of LambdaPi syntax tree a la "<https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf Trees That Grow>" by S. Najd and S. Peyton-Jones.
-}
module Language.Lambda.Syntax.LambdaPi (
  -- * AST
  Name (..),
  Expr (..),
  XExpr,

  -- ** TTG types
  NoExtField (..),
  NoExtCon (),
  noExtCon,

  -- ** Primitives
  Prim (..),

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

  -- *** Let-expressions
  XLet,
  LetName,
  LetRHS,
  LetBody,

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

  -- *** Records
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
  XOpen,
  OpenRecord,
  OpenBody,

  -- *** Variants
  XVariant,
  VariantTags (..),
  VariantArgType,

  -- **** Constructors
  XInj,
  InjArg,

  -- **** Eliminator
  XCase,
  CaseArg,
  CaseAlts (..),
  CaseAlt (..),
  XCaseAlt,
  CaseAltVarName,
  CaseAltBody,

  -- * Pretty-printing
  pprint,
  VarLike (..),
  DocM (..),
  HasBindeeType (..),
  AlphaName (..),
  PrettyEnv (..),
  instantiate,
) where

import Control.Arrow ((>>>))
import Control.Lens
import Control.Monad (forM_)
import Control.Monad.Reader.Class
import Data.Function (on)
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ord (comparing)
import Data.Semigroup.Generic
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.String (IsString, fromString)
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic, Rep)
import GHC.Generics.Constraint
import RIO (NFData)
import Text.PrettyPrint.Monadic

{-
TODO:
Σ-types,
variant weakening,
dependent records,
record shrinking, record update
-}
data Expr phase
  = Ann (XAnn phase) (AnnLHS phase) (AnnRHS phase)
  | Star (XStar phase)
  | Var (XVar phase) (Id phase)
  | App (XApp phase) (AppLHS phase) (AppRHS phase)
  | Lam (XLam phase) (LamBindName phase) (LamBindType phase) (LamBody phase)
  | Pi (XPi phase) (PiVarName phase) (PiVarType phase) (PiRHS phase)
  | Let (XLet phase) (LetName phase) (LetRHS phase) (LetBody phase)
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
  | -- FIXME: we need the explicit list of fields after structural subtyping is introduced; otherwise the system is unsound!
    Open (XOpen phase) (OpenRecord phase) (OpenBody phase)
  | Variant (XVariant phase) (VariantTags phase)
  | Inj (XInj phase) Text (InjArg phase)
  | Case (XCase phase) (CaseArg phase) (CaseAlts phase)
  | XExpr (XExpr phase)
  deriving (Generic)

-- | Names that has no effects for alpha-equivalence used only for the display purposes.
data AlphaName
  = AlphaName {runAlphaName :: Text}
  | Anonymous
  deriving (Show, Generic)

instance VarLike AlphaName where
  varName (AlphaName t) = pure $ Just t
  varName Anonymous = pure $ Nothing

instance IsString AlphaName where
  fromString = AlphaName . fromString

-- | N.B. Everything is regarded to be equal
instance Eq AlphaName where
  (==) = const $ const True

-- | N.B. Everything is regarded to be equal
instance Ord AlphaName where
  compare = const $ const EQ
  (<) = const $ const False
  (<=) = const $ const True
  (>) = const $ const False
  (>=) = const $ const True

instance GPlated (Expr phase) (Rep (Expr phase)) => Plated (Expr phase) where
  plate = gplate
  {-# INLINE plate #-}

deriving instance FieldC Show (Expr phase) => Show (Expr phase)

deriving instance FieldC Eq (Expr phase) => Eq (Expr phase)

deriving instance FieldC Ord (Expr phase) => Ord (Expr phase)

deriving anyclass instance FieldC Hashable (Expr phase) => Hashable (Expr phase)

instance Pretty e Prim where
  pretty Unit = "Unit"
  pretty Tt = "tt"

data Prim = Unit | Tt
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

instance Pretty e NoExtCon where
  pretty = noExtCon

data Name = Global Text | Local Int | Quote Int | PrimName Prim
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

data NoExtField = NoExtField
  deriving (Show, Eq, Ord, Generic)

data NoExtCon
  deriving (Show, Eq, Ord, Generic)

noExtCon :: NoExtCon -> a
noExtCon = \case {}

type family XAnn phase

type family AnnLHS a

type family AnnRHS a

type family XStar p

type family XVar p

type family Id p

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

type family FreeVar p

type family XApp p

type family AppLHS p

type family AppRHS p

type family XLam p

type family LamBindName p

type family LamBindType p

type family LamBody p

type family XPi p

type family PiVarName p

maybeName :: DepName -> Maybe Text
maybeName = \case
  Indep -> Nothing
  DepAnon -> Nothing
  DepNamed t -> Just t

data DepName = Indep | DepAnon | DepNamed Text
  deriving (Show, Eq, Ord, Generic)

type family PiVarType p

type family PiRHS p

type family XLet p

type family LetName p

type family LetRHS p

type family LetBody p

type family XNat p

type family XZero p

type family XSucc p

type family SuccBody p

type family XNatElim p

type family NatElimRetFamily a

type family NatElimBaseCase a

type family NatElimInductionStep a

type family NatElimInput a

type family XVec p

type family VecType p

type family VecLength p

type family XNil p

type family NilType p

type family XCons p

type family ConsType p

type family ConsLength p

type family ConsHead p

type family ConsTail p

type family XVecElim p

type family VecElimEltType p

type family VecElimRetFamily p

type family VecElimBaseCase p

type family VecElimInductiveStep p

type family VecElimLength p

type family VecElimInput p

type family XRecord p

type family RecordFieldType p

newtype RecordFieldTypes p = RecordFieldTypes {recFieldTypes :: [(Text, RecordFieldType p)]}
  deriving (Generic)

deriving instance
  Show (RecordFieldType p) => Show (RecordFieldTypes p)

instance Eq (RecordFieldType p) => Eq (RecordFieldTypes p) where
  (==) = (==) `on` Map.fromList . recFieldTypes

instance Ord (RecordFieldType p) => Ord (RecordFieldTypes p) where
  compare = comparing $ Map.fromList . recFieldTypes

type family XProjField p

type family ProjFieldRecord p

type family XMkRecord p

type family RecordField p

newtype MkRecordFields p = MkRecordFields {mkRecFields :: [(Text, RecordField p)]}
  deriving (Generic)

deriving instance Show (RecordField p) => Show (MkRecordFields p)

instance Eq (RecordField p) => Eq (MkRecordFields p) where
  (==) = (==) `on` Map.fromList . mkRecFields

instance Ord (RecordField p) => Ord (MkRecordFields p) where
  compare = comparing $ Map.fromList . mkRecFields

deriving anyclass instance NFData (RecordField p) => NFData (MkRecordFields p)

deriving anyclass instance Hashable (RecordField p) => Hashable (MkRecordFields p)

type family XOpen p

type family OpenRecord p

type family OpenBody p

type family XVariant p

newtype VariantTags p = VariantTags {variantTags :: [(Text, VariantArgType p)]}
  deriving (Generic)

deriving instance Show (VariantArgType p) => Show (VariantTags p)

instance Eq (VariantArgType p) => Eq (VariantTags p) where
  (==) = (==) `on` Map.fromList . variantTags

instance Ord (VariantArgType p) => Ord (VariantTags p) where
  compare = comparing $ Map.fromList . variantTags

type family VariantArgType p

type family XInj p

type family InjArg p

type family XCase p

type family CaseArg p

type family XCaseAlt p

type family CaseAltVarName p

type family CaseAltBody p

data CaseAlt p = CaseAlt
  { xCaseAlt :: XCaseAlt p
  , altName :: CaseAltVarName p
  , altBody :: CaseAltBody p
  }
  deriving (Generic)

deriving instance FieldC Show (CaseAlt p) => Show (CaseAlt p)

deriving instance FieldC Eq (CaseAlt p) => Eq (CaseAlt p)

deriving instance FieldC Ord (CaseAlt p) => Ord (CaseAlt p)

deriving anyclass instance FieldC Hashable (CaseAlt p) => Hashable (CaseAlt p)

newtype CaseAlts p = CaseAlts {getCaseAlts :: [(Text, CaseAlt p)]}
  deriving (Generic)

deriving instance FieldC Show (CaseAlt p) => Show (CaseAlts p)

deriving instance FieldC Eq (CaseAlt p) => Eq (CaseAlts p)

deriving instance FieldC Ord (CaseAlt p) => Ord (CaseAlts p)

deriving anyclass instance FieldC Hashable (CaseAlt p) => Hashable (CaseAlts p)

type family XExpr p

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
      Just (t, n) -> pure $ Just $ t <> if n > 0 then "_" <> T.pack (show n) else mempty
      Nothing ->
        pure $
          Just $
            "<<Local: " <> T.pack (show i) <> ">>"
  varName (Global t) = pure $ Just t
  varName q@Quote {} = error $ "Could not occur: " <> show q
  varName (PrimName p) = pure $ Just $ T.pack $ show $ pprint p

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

infixl 6 <@>

(<@>) :: DocM e () -> DocM e () -> DocM e ()
l <@> r =
  withPrecParens 12 $
    l <+> withPrecedence 13 r

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
  , VarLike (LetName phase)
  , Pretty PrettyEnv (LetRHS phase)
  , Pretty PrettyEnv (LetBody phase)
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
  , Pretty PrettyEnv (OpenRecord phase)
  , Pretty PrettyEnv (OpenBody phase)
  , Pretty PrettyEnv (VariantArgType phase)
  , Pretty PrettyEnv (InjArg phase)
  , Pretty PrettyEnv (CaseArg phase)
  , VarLike (CaseAltVarName phase)
  , Pretty PrettyEnv (CaseAltBody phase)
  , Pretty PrettyEnv (XExpr phase)
  ) =>
  Pretty PrettyEnv (Expr phase)
  where
  pretty (Ann _ l r) =
    withPrecParens 10 $
      withPrecedence 11 (pretty l) <+> colon <+> pretty r
  pretty Star {} = char '★'
  pretty (Var _ v) = text . fromMaybe "x" =<< varName v
  pretty (App _ l r) = pretty l <@> pretty r
  pretty (Lam _ mv mp body) = withPrecParens 4 $ do
    let mArgTy = bindeeType mp
    var <- fromMaybe "x" <$> varName mv
    lvl <- views (#levels . at var) (fromMaybe 0)
    let varN
          | lvl > 0 = var <> "_" <> tshow lvl
          | otherwise = var
    hang
      ( ( char 'λ'
            <+> appWhen
              (isJust mArgTy)
              parens
              ( text varN <+> forM_ mArgTy \ty ->
                  colon <+> pretty ty
              )
        )
          <> char '.'
      )
      2
      $ instantiate var (pretty body)
  pretty (Pi _ mv mp body) = withPrecParens 4 $ do
    -- TODO: check occurrence of mv in body and
    -- use arrows if absent!
    let mArgTy = bindeeType mp
    var <- fromMaybe "x" <$> varName mv
    lvl <- views (#levels . at var) (fromMaybe 0)
    let varN
          | lvl > 0 = var <> "_" <> T.pack (show lvl)
          | otherwise = var
    hang
      ( ( char 'Π'
            <+> appWhen
              (isJust mArgTy)
              parens
              ( text varN <+> forM_ mArgTy \ty ->
                  colon <+> pretty ty
              )
        )
          <> char '.'
      )
      2
      $ instantiate var (pretty body)
  pretty (Let _ n b e) = do
    var <- fromMaybe "x" <$> varName n
    lvl <- views (#levels . at var) (fromMaybe 0)
    let varN
          | lvl > 0 = var <> "_" <> tshow lvl
          | otherwise = var
    sep
      [ "let" <+> text varN <+> "=" <+> pretty b
      , "in" <+> instantiate var (pretty e)
      ]
  pretty Nat {} = text "ℕ"
  pretty Zero {} = text "0"
  -- FIXME: compress numerals
  pretty (Succ _ e) = text "succ" <@> pretty e
  pretty (NatElim _ t b i n) =
    text "natElim" <@> pretty t <@> pretty b <@> pretty i <@> pretty n
  pretty (Vec _ a n) =
    text "Vec" <@> pretty a <@> pretty n
  pretty (Nil _ a) =
    text "nil" <@> pretty a
  pretty (Cons _ a n x xs) =
    text "cons" <@> pretty a <@> pretty n <@> pretty x <@> pretty xs
  pretty (VecElim _ a t b i n xs) =
    text "vecElim"
      <@> pretty a
      <@> pretty t
      <@> pretty b
      <@> pretty i
      <@> pretty n
      <@> pretty xs
  pretty (Record _ (RecordFieldTypes flds)) =
    braces $
      sep $
        punctuate
          comma
          [ text f <+> colon <+> pretty e
          | (f, e) <- flds
          ]
  pretty (MkRecord _ (MkRecordFields flds)) =
    "record"
      <+> braces
        ( sep $
            punctuate
              comma
              [ text f <+> equals <+> pretty e
              | (f, e) <- flds
              ]
        )
  pretty (ProjField _ e fld) =
    withPrecParens 12 (pretty e <> "#" <> text fld)
  pretty (Open _ recd body) =
    withPrecParens 11 $
      "open" <+> pretty recd <+> "{..}" <+> "in" <+> pretty body
  pretty (Variant _ (VariantTags vts)) =
    "(|"
      <> sep
        ( punctuate
            "|"
            [(text v <> colon) <+> pretty t | (v, t) <- vts]
        )
      <> "|)"
  pretty (Inj _ tag b) =
    "(|" <+> text tag <+> equals <+> pretty b <+> "|)"
  pretty (Case _ e (CaseAlts alts)) =
    sep
      [ "case" <+> pretty e <+> "of"
      , braces $
          sep $
            punctuate
              semi
              [ do
                var <- fromMaybe "x" <$> varName v
                nest 2 $
                  text tag
                    <+> text var
                    <+> "→"
                    <+> instantiate var (pretty a)
              | (tag, CaseAlt _ v a) <- alts
              ]
      ]
  pretty (XExpr e) = pretty e

tshow :: Show a => a -> Text
tshow = T.pack . show

instantiate :: Text -> DocM PrettyEnv () -> DocM PrettyEnv ()
instantiate var act = do
  lvl <- views (#levels . at var) (fromMaybe 0)
  local
    ( #levels . at var ?~ (lvl + 1)
        >>> #boundVars %~ (Seq.<|) (var, lvl)
    )
    act

pprint :: Pretty PrettyEnv a => a -> Doc
pprint = execDocM (mempty @PrettyEnv) . pretty

{-
occursChk :: Int -> Term 'Checkable -> Bool
occursChk i (Inf te') = occursInf i te'
occursChk i (Lam te') = occursChk (i + 1) te'
occursChk i (MkRecord flds) = any (occursChk i . snd) flds

occursInf :: Int -> Term 'Inferable -> Bool
occursInf i (te' ::: te2) = occursChk i te' || occursChk i te2
occursInf _ Star = False
occursInf i (LamAnn te' te2) =
  occursChk i te' || occursInf (i + 1) te2
occursInf i (Pi te' te2) =
  occursChk i te' || occursChk (i + 1) te2
occursInf i (NatElim te' te2 te3 te4) =
  occursChk i te' || occursChk i te2 || occursChk i te3 || occursChk i te4
occursInf i (Bound n)
  | i == n = True
  | otherwise = False
occursInf _ Free {} = False
occursInf i (te' :@: te2) = occursInf i te' || occursChk i te2
occursInf _ Nat = False
occursInf _ Zero = False
occursInf i (Succ te') = occursChk i te'
occursInf i (Vec te' te2) = occursChk i te' || occursChk i te2
occursInf i (Nil te') = occursChk i te'
occursInf i (Cons te' te2 te3 te4) = occursChk i te' || occursChk i te2 || occursChk i te3 || occursChk i te4
occursInf i (VecElim te' te2 te3 te4 te5 te6) =
  occursChk i te'
    || occursChk i te2
    || occursChk i te3
    || occursChk i te4
    || occursChk i te5
    || occursChk i te6
occursInf i (Variant vars) = any (occursChk i . snd) vars
occursInf i (Record flds) = any (occursChk i . snd) flds
occursInf i (e :#: _) = occursInf i e

-}