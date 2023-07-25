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
  XName,
  XGlobal,
  XBound,
  XPrimName,
  Expr (..),
  _Var,
  _XName,
  XExpr,

  -- ** TTG types
  NoExtField (..),
  NoExtCon (),
  noExtCon,
  Located (..),

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

  -- *** Sigma-types
  XSigma,
  SigmaVarName,
  SigmaVarType,
  SigmaBody,

  -- **** Construction
  XPair,
  PairFst,
  PairSnd,

  -- *** Let-expressions
  XLet,
  LetName,
  LetRHS,
  LetBody,

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
import Data.Bifoldable
import Data.Bitraversable
import Data.Data (Data)
import Data.Function (on)
import Data.Functor.Apply qualified as Apply
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ord (comparing)
import Data.Semigroup.Bifoldable
import Data.Semigroup.Bitraversable
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

data Located e a = Loc {location :: !e, unLoc :: !a}
  deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable)
  deriving anyclass (Bitraversable)

instance Bifunctor Located where
  bimap = bimapDefault
  {-# INLINE bimap #-}

instance Bifoldable Located where
  bifoldMap = bifoldMapDefault
  {-# INLINE bifoldMap #-}

instance Bifoldable1 Located where
  bifoldMap1 = bifoldMap1Default
  {-# INLINE bifoldMap1 #-}

instance Bitraversable1 Located where
  bitraverse1 f g (Loc l a) = Loc <$> f l Apply.<.> g a
  {-# INLINE bitraverse1 #-}

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
  | Var (XVar phase) (Name phase)
  | App (XApp phase) (AppLHS phase) (AppRHS phase)
  | Lam (XLam phase) (LamBindName phase) (LamBindType phase) (LamBody phase)
  | Pi (XPi phase) (PiVarName phase) (PiVarType phase) (PiRHS phase)
  | Sigma (XSigma phase) (SigmaVarName phase) (SigmaVarType phase) (SigmaBody phase)
  | Pair (XPair phase) (PairFst phase) (PairSnd phase)
  | Let (XLet phase) (LetName phase) (LetRHS phase) (LetBody phase)
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

_Var :: Generic (Expr p) => Prism' (Expr p) (XVar p, Name p)
_Var = #_Var

deriving instance FieldC NFData (Expr p) => NFData (Expr p)

deriving instance (Data p, FieldC Data (Expr p)) => Data (Expr p)

-- | Names that has no effects for alpha-equivalence used only for the display purposes.
data AlphaName
  = AlphaName {runAlphaName :: Text}
  | Anonymous
  deriving (Show, Generic, Data)
  deriving anyclass (NFData)

instance VarLike AlphaName where
  varName (AlphaName t) = pure $ Just t
  varName Anonymous = pure Nothing

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
  pretty NatElim = "natElim"
  -- FIXME: Compress numerals
  pretty Nat = "ℕ"
  pretty Succ = "succ"
  pretty Zero = "zero"

-- pretty (UserDefined t) = pretty t

data Prim = Unit | Tt | Nat | Succ | Zero | NatElim
  deriving (Show, Eq, Ord, Generic, Data)
  deriving anyclass (Hashable)
  deriving anyclass (NFData)

instance Pretty e NoExtCon where
  pretty = noExtCon

data Name p
  = Global (XGlobal p) Text
  | Bound (XBound p) Int
  | PrimName (XPrimName p) Prim
  | XName (XName p)
  deriving (Generic)

_XName :: Prism' (Name p) (XName p)
_XName = #_XName

deriving anyclass instance FieldC NFData (Name p) => NFData (Name p)

deriving instance (Data p, FieldC Data (Name p)) => Data (Name p)

type family XGlobal p

type family XBound p

type family XPrimName p

deriving instance FieldC Show (Name p) => Show (Name p)

deriving instance FieldC Eq (Name p) => Eq (Name p)

deriving instance FieldC Ord (Name p) => Ord (Name p)

deriving anyclass instance FieldC Hashable (Name p) => Hashable (Name p)

type family XName p

data NoExtField = NoExtField
  deriving (Show, Eq, Ord, Generic, Data)
  deriving anyclass (NFData)

data NoExtCon
  deriving (Show, Eq, Ord, Generic, Data)
  deriving anyclass (NFData)

instance VarLike NoExtCon where
  varName = noExtCon

noExtCon :: NoExtCon -> a
noExtCon = \case {}

type family XAnn phase

type family AnnLHS a

type family AnnRHS a

type family XStar p

type family XVar p

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
  deriving (Show, Eq, Ord, Generic, Data)

type family PiVarType p

type family PiRHS p

type family XSigma p

type family SigmaVarName p

type family SigmaVarType p

type family XPair p

type family PairFst p

type family PairSnd p

type family SigmaBody p

type family XLet p

type family LetName p

type family LetRHS p

type family LetBody p

type family XRecord p

type family RecordFieldType p

newtype RecordFieldTypes p = RecordFieldTypes {recFieldTypes :: [(Text, RecordFieldType p)]}
  deriving (Generic)

deriving instance (Data (RecordFieldType p), Data p) => Data (RecordFieldTypes p)

deriving newtype instance (NFData (RecordFieldType p)) => NFData (RecordFieldTypes p)

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

deriving instance (Data p, Data (RecordField p)) => Data (MkRecordFields p)

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

deriving newtype instance NFData (VariantArgType p) => NFData (VariantTags p)

deriving instance (Data (VariantArgType p), Data p) => Data (VariantTags p)

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

deriving anyclass instance
  FieldC NFData (CaseAlt p) => NFData (CaseAlt p)

deriving instance (Data p, FieldC Data (CaseAlt p)) => Data (CaseAlt p)

deriving instance FieldC Show (CaseAlt p) => Show (CaseAlt p)

deriving instance FieldC Eq (CaseAlt p) => Eq (CaseAlt p)

deriving instance FieldC Ord (CaseAlt p) => Ord (CaseAlt p)

deriving anyclass instance FieldC Hashable (CaseAlt p) => Hashable (CaseAlt p)

newtype CaseAlts p = CaseAlts {getCaseAlts :: [(Text, CaseAlt p)]}
  deriving (Generic)

deriving newtype instance NFData (CaseAlt p) => NFData (CaseAlts p)

deriving instance (Data p, Data (CaseAlt p)) => Data (CaseAlts p)

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

instance VarLike (XName p) => VarLike (Name p) where
  {-   varName (Local _ i) = do
      mtn <- preview $ #boundVars . ix i
      case mtn of
        Just (t, n) -> pure $ Just $ t <> if n > 0 then "_" <> T.pack (show n) else mempty
        Nothing ->
          pure $
            Just $
              "<<Local: " <> T.pack (show i) <> ">>" -}
  varName (Bound _ j) = do
    mtn <- preview $ #boundVars . ix j
    case mtn of
      Just (t, n) -> pure $ Just $ t <> if n > 0 then "_" <> T.pack (show n) else mempty
      Nothing ->
        pure $
          Just $
            "<<Bound: " <> T.pack (show j) <> ">>"
  varName (Global _ t) = pure $ Just t
  varName (PrimName _ p) = pure $ Just $ T.pack $ show $ pprint p
  varName (XName xn) = varName xn

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
  , VarLike (XName phase)
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
  , VarLike (SigmaVarName phase)
  , HasBindeeType (SigmaVarType phase)
  , Pretty PrettyEnv (BindeeType (SigmaVarType phase))
  , Pretty PrettyEnv (SigmaBody phase)
  , Pretty PrettyEnv (PairFst phase)
  , Pretty PrettyEnv (PairSnd phase)
  , VarLike (LetName phase)
  , Pretty PrettyEnv (LetRHS phase)
  , Pretty PrettyEnv (LetBody phase)
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
  pretty (Sigma _ mv mp body) = withPrecParens 4 $ do
    -- TODO: check occurrence of mv in body and
    -- use arrows if absent!
    let mArgTy = bindeeType mp
    var <- fromMaybe "x" <$> varName mv
    lvl <- views (#levels . at var) (fromMaybe 0)
    let varN
          | lvl > 0 = var <> "_" <> T.pack (show lvl)
          | otherwise = var
    hang
      ( ( char 'Σ'
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
  pretty (Pair _ l r) = do
    "⟨" <+> pretty l <+> pretty r <+> "⟩"
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
  -- FIXME: compress numerals
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
