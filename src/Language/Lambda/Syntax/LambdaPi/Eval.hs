{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}

module Language.Lambda.Syntax.LambdaPi.Eval (
  -- * Type checking and inference
  Env' (..),
  Env,
  Value' (..),
  Value,
  (@@),
  Type,
  Type',
  Neutral' (..),
  Neutral,
  eval,
  thawLocal,
  thawLocalVal,
  BinderTypeSpec (..),
  EvalVars (..),
  vapps,
  vfree,
  nSucc,
  nZero,
  vSucc,
  vZero,

  -- * ASTs
  quote,
  injValueWith,
  injBinder,
  projValueM,
  ThawEnv (..),
  Eval,
  Eval',
  CaseTypeInfo (..),
  SplitTypeInfo (..),
  substBound,
  inferPrim,
  evalNatElim,
) where

import Control.Lens hiding (Context)
import Control.Monad.Reader (Reader, ask, asks, local, runReader)
import Data.Bifunctor qualified as Bi
import Data.Data (Data)
import Data.Function (fix, on)
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Level
import Data.List
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe
import Data.Ord (comparing)
import Data.Semigroup.Generic
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import Language.Lambda.Syntax.LambdaPi
import RIO (NFData (..), deepseq, tshow)
import Text.PrettyPrint.Monadic (Pretty (..))

type Value = Value' Z

data Value' n
  = VLam (BinderTypeSpec n) AlphaName (Value' n -> Value' n)
  | VStar
  | VPi AlphaName (Value' n) (Value' n -> Value' n)
  | VSigma AlphaName (Value' n) (Value' n -> Value' n)
  | VPair (BinderTypeSpec n) AlphaName (Value' n) (Value' n)
  | VRecord (HashMap Text (Value' n))
  | VMkRecord (HashMap Text (Type' n)) (HashMap Text (Value' n))
  | VVariant (HashMap Text (Value' n))
  | VInj (HashMap Text (Type' n)) Text (Value' n)
  | VNeutral (Neutral' n)
  deriving (Generic)

instance NFData (BinderTypeSpec n) where
  rnf BinderTypeSpec {..} = rnf argType `seq` rnfTyFun argType bodyType

rnfTyFun :: Type' n -> (Type' n -> Type' n) -> ()
rnfTyFun argTy f = f `deepseq` f (vfree argTy (Bound NoExtField (-1))) `deepseq` ()

rnfTyFun2 :: Type' n -> Type' n -> (Type' n -> Type' n -> Type' n) -> ()
rnfTyFun2 fstTy sndTy f = f `deepseq` f (vfree fstTy (Bound NoExtField (-1))) (vfree sndTy (Bound NoExtField (-2))) `deepseq` ()

instance NFData (Value' n) where
  rnf (VLam lts a b) = lts `deepseq` a `deepseq` rnfTyFun (argType lts) b
  rnf (VPi an a b) = an `deepseq` a `deepseq` rnfTyFun a b
  rnf (VSigma an a b) = an `deepseq` a `deepseq` rnfTyFun a b
  rnf (VPair ts mn l r) = ts `deepseq` mn `deepseq` l `deepseq` rnf r
  rnf VStar = ()
  rnf (VRecord flds) = rnf flds
  rnf (VMkRecord fldTys flds) = fldTys `deepseq` rnf flds
  rnf (VVariant tags) = rnf tags
  rnf (VInj alts l tag) = alts `deepseq` l `deepseq` rnf tag
  rnf (VNeutral n) = rnf n

typeOf :: Value' n -> Type' n
typeOf (VLam BinderTypeSpec {..} x _) = VPi x argType bodyType
typeOf VStar = VStar
typeOf VPi {} = VStar
typeOf VSigma {} = VStar
typeOf (VPair BinderTypeSpec {..} x _ _) = VSigma x argType bodyType
typeOf VRecord {} = VStar
typeOf (VMkRecord fldTys _) = VRecord fldTys
typeOf VVariant {} = VStar
typeOf (VInj tags _ _) = VVariant tags
typeOf (VNeutral n) = typeOfNeutral n

nSucc :: Neutral' n
nSucc = NFree (VPi Anonymous VNat (const VNat)) (PrimName NoExtField Succ)

pattern VNat :: Value' n
pattern VNat = VNeutral (NFree VStar (PrimName NoExtField Nat))

vSucc :: Value' n
vSucc = VNeutral nSucc

nZero :: Neutral' n
nZero = NFree VNat $ PrimName NoExtField Zero

vZero :: Value' n
vZero = VNeutral $ NFree VNat $ PrimName NoExtField Zero

instance Show (Value' n) where
  show = show . pprint . quote 0

instance (Pretty e (Expr (Eval' n))) => Pretty e (Value' n) where
  pretty = pretty . quote 0

data SplitTypeInfo n = SplitTypeInfo
  { splitFstType :: Type' n
  , splitSndType :: Type' n -> Type' n
  , splitRetType :: Type' n
  }
  deriving (Generic)
  deriving anyclass (NFData)

instance Show (SplitTypeInfo n) where
  showsPrec _ spc =
    let (arg, bdy) = splitTypeRank spc
     in showString "BinderTypeSpec { "
          . showString "scrutinee = "
          . shows arg
          . showString ", "
          . showString "bodyType = "
          . shows bdy
          . showString " }"

instance Eq (SplitTypeInfo n) where
  (==) :: SplitTypeInfo n -> SplitTypeInfo n -> Bool
  (==) = (==) `on` splitTypeRank

instance Ord (SplitTypeInfo n) where
  compare = comparing splitTypeRank

splitTypeRank :: SplitTypeInfo n -> (Type' n, Type' n)
splitTypeRank SplitTypeInfo {..} =
  (VSigma Anonymous splitFstType splitSndType, splitRetType)

type Neutral = Neutral' Z

data Neutral' n
  = NFree (Type' n) (Name (Eval' n))
  | NApp (Type' n) (Neutral' n) (Value' n)
  | NProjField (Type' n) (Neutral' n) Text
  | NSplit (SplitTypeInfo n) (Neutral' n) AlphaName AlphaName (Value' n -> Value' n -> Value' n)
  | NCase (CaseTypeInfo n) (Neutral' n) (HM.HashMap Text (Value' n -> Value' n))
  -- FIXME: Work out what NOpen should be
  deriving (Generic)

instance NFData (Neutral' n) where
  rnf (NFree ty n) = ty `deepseq` rnf n
  rnf (NApp ty l r) = ty `deepseq` l `deepseq` rnf r
  rnf (NProjField ty p l) = ty `deepseq` p `deepseq` rnf l
  rnf (NCase ty e xs) = ty `deepseq` e `deepseq` rnf (fmap (rnfTyFun VStar) xs)
  rnf (NSplit cty s l r b) =
    cty `deepseq`
      s `deepseq`
        l `deepseq`
          r `deepseq`
            rnfTyFun2
              (splitFstType cty)
              (splitSndType cty (vfree (splitFstType cty) $ XName $ Quote 0))
              b

nPrim :: Type' n -> Prim -> Neutral' n
nPrim ty p = NFree ty $ PrimName NoExtField p

inferPrim :: (HasCallStack) => Prim -> Type' n
inferPrim Tt = VNeutral $ nPrim VStar Unit
inferPrim Unit = VStar
inferPrim Nat = VStar
inferPrim Zero = VNat
inferPrim Succ = VPi Anonymous VNat (const VNat)
inferPrim NatElim = natElimType

typeOfNeutral :: Neutral' n -> Type' n
typeOfNeutral (NFree retTy _) = retTy
typeOfNeutral (NApp retTy _ _) = retTy
typeOfNeutral (NProjField retTy _ _) = retTy
typeOfNeutral (NCase CaseTypeInfo {..} _ _) = caseRetTy
typeOfNeutral (NSplit ty _ _ _ _) = splitRetType ty

vfree :: Type' n -> Name (Eval' n) -> Value' n
vfree = fmap VNeutral . NFree

type Env = Env' Z

data Env' n = Env
  { namedBinds :: !(HM.HashMap Text (Value' n))
  , boundValues :: ![Value' n]
  }
  deriving (Show, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid (Env' n)

instance Eq (Value' n) where
  (==) = (==) `on` quote 0

instance Ord (Value' n) where
  compare = comparing $ quote 0

type Type' = Value'

type Type = Value

quote :: Int -> Value' n -> Expr (Eval' n)
quote i (VLam ls@BinderTypeSpec {..} mv f) =
  Lam ls mv (quote i argType) $
    quote (i + 1) $
      f $
        vfree argType $
          XName $
            Quote i
quote _ VStar = Star NoExtField
quote i (VPi mv v f) =
  Pi NoExtField mv (quote i v) $
    quote (i + 1) $
      f $
        vfree v $
          XName $
            Quote i
quote i (VSigma mv v f) =
  Sigma NoExtField mv (quote i v) $
    quote (i + 1) $
      f $
        vfree v $
          XName $
            Quote i
quote i (VPair ls _mv l r) =
  Pair ls (quote i l) (quote i r)
quote i (VNeutral n) = quoteNeutral i n
quote i (VRecord flds) =
  Record NoExtField $
    RecordFieldTypes $
      HM.toList $
        fmap (quote i) flds
quote i (VMkRecord fldTys flds) =
  MkRecord fldTys $
    MkRecordFields $
      HM.toList $
        fmap (quote i) flds
quote i (VVariant flds) =
  Variant NoExtField $
    VariantTags $
      HM.toList $
        fmap (quote i) flds
quote i (VInj alts l e) =
  Inj alts l $ quote i e

quoteNeutral :: Int -> Neutral' n -> Expr (Eval' n)
quoteNeutral i (NFree ty x) = boundFree ty i x
quoteNeutral i (NApp ty n v) = App ty (quoteNeutral i n) (quote i v)
quoteNeutral i (NProjField ty r f) =
  ProjField ty (quoteNeutral i r) f
quoteNeutral i (NSplit ty@SplitTypeInfo {..} s l r f) =
  Split ty (quoteNeutral i s) l r $
    quote (i + 2) $
      f
        (vfree splitFstType (XName $ Quote i))
        ( vfree
            (splitSndType $ vfree splitFstType $ XName $ Quote i)
            (XName $ Quote (i + 1))
        )
quoteNeutral i (NCase ty@CaseTypeInfo {..} v alts) =
  Case ty (quoteNeutral i v) $
    CaseAlts $
      HM.toList $
        HM.intersectionWith
          ( \argType f ->
              CaseAlt NoExtField Anonymous $
                quote (i + 1) $
                  f $
                    vfree argType $
                      XName $
                        Quote i
          )
          caseAltArgs
          alts

boundFree :: Type' n -> Int -> Name (Eval' n) -> Expr (Eval' n)
boundFree ty i (XName (Quote k)) = Var ty $ Bound NoExtField $ i - k - 1
boundFree ty _ x = Var ty x

eval :: (HasCallStack) => Env' n -> Expr (Eval' n) -> Value' n
eval ctx (Ann _ e _) = eval ctx e
eval _ Star {} = VStar
eval ctx (Var ty fv) =
  case fv of
    PrimName _ p -> VNeutral $ nPrim ty p
    Global _ g | Just v <- ctx ^. #namedBinds . at g -> v
    Bound _ n ->
      fromMaybe (error $ "eval/BoundVar: oob: " <> show (n, pprint ty, ctx)) $
        ctx ^? #boundValues . ix n
    _ -> vfree ty fv
eval ctx (App _ f x) = eval ctx f @@ eval ctx x
eval ctx (Lam ty mv _ e) = VLam ty mv $ \x ->
  eval
    (ctx & #boundValues %~ (x <|))
    e
eval ctx (Pi _ mv t t') =
  VPi mv (eval ctx t) $ \x -> eval (ctx & #boundValues %~ (x <|)) t'
eval ctx (Sigma _ mv t t') =
  VSigma mv (eval ctx t) $ \x -> eval (ctx & #boundValues %~ (x <|)) t'
eval ctx (Pair ty l r) =
  VPair ty Anonymous (eval ctx l) (eval ctx r)
eval ctx (Let _ _ e b) =
  eval
    (ctx & #boundValues %~ (eval ctx e <|))
    b
eval ctx (Record _ flds) = VRecord $ HM.fromList $ map (Bi.second $ eval ctx) $ recFieldTypes flds
eval ctx (MkRecord fldTys recs) =
  VMkRecord fldTys $ HM.fromList $ map (Bi.second $ eval ctx) $ mkRecFields recs
eval ctx (ProjField retTy e f) = evalProjField retTy f $ eval ctx e
eval ctx (Open _ rcd bdy) =
  case eval ctx rcd of
    -- FIXME: we need the explicit list of fields after structural subtyping is introduced; otherwise the system is unsound!
    VMkRecord _ flds ->
      let ctx' = ctx & #namedBinds %~ (flds <>)
       in eval ctx' bdy
    otr ->
      error $
        "Impossible: open requires a record, but got a term of type: "
          <> show (pprint $ quote 0 otr)
eval ctx (Variant _ flds) = VVariant $ HM.fromList $ map (Bi.second $ eval ctx) $ variantTags flds
eval ctx (Inj alts t e) = VInj alts t $ eval ctx e
eval ctx (Split cinfo scrtn lName rName body) =
  evalSplit cinfo (eval ctx scrtn) lName rName $ \_fst _snd ->
    eval (ctx & #boundValues %~ ((_snd <|) . (_fst <|))) body
eval ctx (Case cinfo e (CaseAlts alts)) =
  evalCase cinfo (eval ctx e) $
    HM.fromList alts <&> \(CaseAlt _ _ b) v ->
      eval (ctx & #boundValues %~ (v <|)) b
eval _ (XExpr c) = noExtCon c

evalSplit :: SplitTypeInfo n -> Value' n -> AlphaName -> AlphaName -> (Value' n -> Value' n -> Value' n) -> Value' n
evalSplit sinfo v0 lName rName body =
  case v0 of
    VNeutral n -> VNeutral $ NSplit sinfo n lName rName body
    VPair _ _ l r -> body l r
    v -> error $ "Impossible: split-expression expects dependent-pair (sigma-type) as a scrutinee, but got: " <> show (pprint v)

evalCase :: CaseTypeInfo n -> Value' n -> HashMap Text (Value' n -> Value' n) -> Value' n
evalCase cinfo v0 alts = case v0 of
  VInj _ t v ->
    case HM.lookup t alts of
      Nothing ->
        error $
          "Impossible: missing alternative for `"
            <> T.unpack t
            <> "' in the given case alternative: "
            <> show (HM.keys alts)
      Just f -> f v
  VNeutral v -> VNeutral $ NCase cinfo v alts
  v -> error $ "Impossible: neither inj or neutral term given as a scrutinee of case-expression: " <> show (pprint v)

evalNatElim :: Value' n -> Value' n -> Value' n -> Value' n -> Value' n
evalNatElim t t0 tStep = fix $ \recur kVal ->
  case kVal of
    VNeutral (NFree _ (PrimName _ Zero)) -> t0
    VNeutral (NApp _ (NFree _ (PrimName _ Succ)) l) -> tStep @@ l @@ recur l
    VNeutral nk ->
      VNeutral $
        NApp
          (t @@ VNeutral nk)
          ( NApp
              (VPi Anonymous VNat (t @@))
              ( NApp
                  ( VPi Anonymous VNat (\l -> (t @@ l) ~> (t @@ (vSucc @@ l)))
                      ~> VPi Anonymous VNat (t @@)
                  )
                  ( NApp
                      ( (t @@ vZero)
                          ~> VPi
                            Anonymous
                            VNat
                            ( \l ->
                                (t @@ l) ~> (t @@ (vSucc @@ l))
                            )
                          ~> VPi Anonymous VNat (t @@)
                      )
                      (NFree natElimType (PrimName NoExtField NatElim))
                      t
                  )
                  t0
              )
              tStep
          )
          (VNeutral nk)
    _ -> error "internal: eval natElim failed!"

infixr 0 ~>

(~>) :: Type' n -> Type' n -> Type' n
(~>) l = VPi Anonymous l . const

natElimType :: (HasCallStack) => Type' n
natElimType =
  VPi (AlphaName "t") (VPi Anonymous VNat $ const VStar) $ \t ->
    VPi (AlphaName "base") (t @@ vZero) $ \_base ->
      VPi
        (AlphaName "step")
        ( VPi (AlphaName "l") VNat $ \l ->
            VPi (AlphaName "tl") (t @@ l) $ \_tl ->
              t @@ (vSucc @@ l)
        )
        $ \_step ->
          VPi (AlphaName "k") VNat $ \k -> t @@ k

evalProjField :: Type' n -> Text -> Value' n -> Value' n
evalProjField retTy f =
  \case
    VMkRecord _ flds ->
      fromMaybe
        ( error $
            "Impossible: given record doesn't have a field `"
              <> T.unpack f
              <> "': "
              <> show (sort $ HM.keys flds)
        )
        $ HM.lookup f flds
    VNeutral n -> VNeutral $ NProjField retTy n f
    v ->
      error $
        "Impossible: non-evaulable record field projection: "
          <> show (f, pprint v)

infixl 9 @@, :@

pattern (:@) :: Neutral' n -> Value' n -> Neutral' n
pattern l :@ r <- NApp _ l r

pattern P :: Prim -> Neutral' n
pattern P p <- NFree _ (PrimName _ p)

(@@) :: (HasCallStack) => Value' n -> Value' n -> Value' n
VLam _ _ f @@ r = f r
VNeutral nlhs@(P NatElim :@ t :@ _ :@ _) @@ VNeutral n =
  VNeutral $ NApp (t @@ VNeutral n) nlhs (VNeutral n)
VNeutral (P NatElim :@ t :@ base :@ ind) @@ n = evalNatElim t base ind n
VNeutral neu @@ r
  | VPi _ _ f <- typeOfNeutral neu =
      VNeutral $ NApp (f r) neu r
l @@ r = error $ "Could not apply: " <> show ((pprint l, typeOf l), (pprint r, typeOf r))

vapps :: NonEmpty (Type' n) -> Type' n
vapps = foldl1 (@@)

newtype ThawEnv n = ThawEnv {curLvl :: Int}
  deriving (Show, Eq, Generic)

type Thawer n = Reader (ThawEnv n)

thawLocalVal :: Value' (S n) -> Value' n
thawLocalVal =
  flip runReader ThawEnv {curLvl = 0} . thawLocalValM

thawLocal :: forall n. Expr (Eval' (S n)) -> Expr (Eval' n)
thawLocal = flip runReader ThawEnv {curLvl = 0} . go
  where
    go :: Expr (Eval' (S n)) -> Thawer n (Expr (Eval' n))
    go (Var ty name) = do
      -- NOTE: This isn't needed if occurs check passed
      Var <$> thawLocalValM ty <*> thawName name
    go (Pi NoExtField mn l r) =
      Pi NoExtField mn <$> go l <*> local (#curLvl +~ 1) (go r)
    go (Lam lamTy mn l r) =
      Lam
        <$> thawLocalBinderTy lamTy
        <*> pure mn
        <*> go l
        <*> local (#curLvl +~ 1) (go r)
    go (Sigma NoExtField mn l r) =
      Sigma NoExtField mn <$> go l <*> local (#curLvl +~ 1) (go r)
    go (Pair ty l r) =
      Pair <$> thawLocalBinderTy ty <*> go l <*> go r
    go (Split ty scrut2 lName rName b) =
      Split
        <$> thawLocalSplitInfo ty
        <*> go scrut2
        <*> pure lName
        <*> pure rName
        <*> local (#curLvl +~ 2) (go b)
    go (Ann e l r) = Ann <$> thawLocalValM e <*> go l <*> go r
    go (App e l r) = App <$> thawLocalValM e <*> go l <*> go r
    go (Let c mn e v) =
      Let <$> thawLocalValM c <*> pure mn <*> go e <*> local (#curLvl +~ 1) (go v)
    go (Star x) = pure $ Star x
    go (Record NoExtField (RecordFieldTypes flds)) =
      Record NoExtField . RecordFieldTypes <$> mapM (mapM go) flds
    go (MkRecord tys (MkRecordFields flds)) =
      MkRecord
        <$> mapM thawLocalValM tys
        <*> (MkRecordFields <$> mapM (mapM go) flds)
    go (ProjField ty e l) =
      ProjField <$> thawLocalValM ty <*> go e <*> pure l
    go (Open ty r b) =
      Open <$> thawLocalValM ty <*> go r <*> go b
    go (Variant NoExtField (VariantTags flds)) =
      Variant NoExtField . VariantTags <$> mapM (mapM go) flds
    go (Inj tags l p) =
      Inj <$> mapM thawLocalValM tags <*> pure l <*> go p
    go (Case caseTy e (CaseAlts alts)) =
      Case
        <$> thawLocalCaseInfo caseTy
        <*> go e
        <*> (CaseAlts <$> local (#curLvl +~ 1) (mapM (mapM goAlt) alts))
    go (XExpr c) = noExtCon c
    goAlt (CaseAlt NoExtField name a) =
      CaseAlt NoExtField name <$> go a

thawLocalSplitInfo :: SplitTypeInfo ('S n) -> Thawer n (SplitTypeInfo n)
thawLocalSplitInfo si = do
  e <- ask
  _fst <- thawLocalValM $ splitFstType si
  let _snd = thawLocalWith (e & #curLvl +~ 1) . splitSndType si . injValueWith e
  _ret <- thawLocalValM $ splitRetType si
  pure SplitTypeInfo {splitFstType = _fst, splitSndType = _snd, splitRetType = _ret}

thawLocalCaseInfo :: CaseTypeInfo (S n) -> Thawer n (CaseTypeInfo n)
thawLocalCaseInfo CaseTypeInfo {..} =
  CaseTypeInfo
    <$> thawLocalValM caseRetTy
    <*> mapM thawLocalValM caseAltArgs

thawLocalBinderTy :: BinderTypeSpec (S n) -> Thawer n (BinderTypeSpec n)
thawLocalBinderTy BinderTypeSpec {..} = do
  env <- ask
  BinderTypeSpec
    <$> thawLocalValM argType
    <*> pure
      (thawLocalWith (env & #curLvl +~ 1) . bodyType . withEnv env . injValueM)

withEnv :: e -> Reader e a -> a
withEnv = flip runReader

thawLocalValM :: Value' (S n) -> Thawer n (Value' n)
thawLocalValM = go
  where
    go VStar = pure VStar
    go (VPi mv argTy f) = do
      env <- ask
      VPi mv
        <$> thawLocalValM argTy
        <*> pure (thawLocalWith (env & #curLvl +~ 1) . f . injValueWith env)
    go (VLam lt name f) = do
      env <- ask
      VLam
        <$> thawLocalBinderTy lt
        <*> pure name
        <*> pure (thawLocalWith (env & #curLvl +~ 1) . f . injValueWith env)
    go (VSigma mv argTy f) = do
      env <- ask
      VSigma mv
        <$> thawLocalValM argTy
        <*> pure (thawLocalWith (env & #curLvl +~ 1) . f . injValueWith env)
    go (VPair lt name l r) = do
      VPair
        <$> thawLocalBinderTy lt
        <*> pure name
        <*> go l
        <*> go r
    go (VRecord flds) = VRecord <$> mapM go flds
    go (VMkRecord fldTys flds) =
      VMkRecord <$> mapM go fldTys <*> mapM go flds
    go (VVariant tags) = VVariant <$> mapM go tags
    go (VInj alts l v) = VInj <$> mapM go alts <*> pure l <*> go v
    go (VNeutral n) = VNeutral <$> thawLocalNeutral n

thawLocalWith :: ThawEnv n -> Value' (S n) -> Value' n
thawLocalWith i = flip runReader i . thawLocalValM

thawLocalNeutral :: Neutral' (S n) -> Thawer n (Neutral' n)
thawLocalNeutral = go
  where
    go (NFree ty v) =
      NFree
        <$> thawLocalValM ty
        <*> thawName v
    go (NApp ty l v) =
      NApp
        <$> thawLocalValM ty
        <*> go l
        <*> thawLocalValM v
    go (NProjField ty p l) =
      NProjField <$> thawLocalValM ty <*> go p <*> pure l
    go (NSplit ty scrut2 ln rn b) = do
      env <- ask
      NSplit
        <$> thawLocalSplitInfo ty
        <*> go scrut2
        <*> pure ln
        <*> pure rn
        <*> pure \l r ->
          runReader
            (thawLocalValM $ b (injValueWith env l) (injValueWith env r))
            env
    go (NCase ty scr alts) = do
      e <- ask
      NCase
        <$> thawLocalCaseInfo ty
        <*> go scr
        <*> pure
          ( fmap
              (dimap (injValueWith e) (thawLocalWith e))
              alts
          )

mapLocal :: (Ordinal n -> Name (Eval' m)) -> Name (Eval' n) -> Name (Eval' m)
mapLocal f = \case
  XName (EvLocal l) -> f l
  XName (Quote a) -> XName $ Quote a
  Global x a -> Global x a
  Bound x a -> Bound x a
  PrimName x a -> PrimName x a

mapLocalM :: (Applicative f) => (Ordinal n -> f (Name (Eval' m))) -> Name (Eval' n) -> f (Name (Eval' m))
mapLocalM f = \case
  XName (EvLocal l) -> f l
  XName (Quote a) -> pure $ XName $ Quote a
  Global x a -> pure $ Global x a
  Bound x a -> pure $ Bound x a
  PrimName x a -> pure $ PrimName x a

forLocal :: Name (Eval' n) -> (Ordinal n -> Name (Eval' m)) -> Name (Eval' m)
forLocal = flip mapLocal

thawName :: Name (Eval' (S n)) -> Thawer n (Name (Eval' n))
thawName =
  mapLocalM $ \k -> do
    case predOrd k of
      Nothing -> views #curLvl $ Bound NoExtField
      Just l -> pure $ XName $ EvLocal l

injValueWith :: ThawEnv n -> Value' n -> Value' (S n)
injValueWith e = withEnv e . injValueM

injValueM :: Value' n -> Thawer n (Value' (S n))
injValueM VStar = pure VStar
injValueM (VPi an argTy body) = VPi an <$> injValueM argTy <*> injBinderM body
injValueM (VSigma an argTy body) = VSigma an <$> injValueM argTy <*> injBinderM body
injValueM (VPair bs an argTy body) =
  VPair <$> injBindTypeInfo bs <*> pure an <*> injValueM argTy <*> injValueM body
injValueM (VLam ty n b) = do
  VLam
    <$> injBindTypeInfo ty
    <*> pure n
    <*> injBinderM b
injValueM (VRecord flds) = VRecord <$> mapM injValueM flds
injValueM (VMkRecord fldTys flds) =
  VMkRecord <$> mapM injValueM fldTys <*> mapM injValueM flds
injValueM (VVariant alts) = VVariant <$> mapM injValueM alts
injValueM (VInj alts tag x) =
  VInj <$> mapM injValueM alts <*> pure tag <*> injValueM x
injValueM (VNeutral n) = VNeutral <$> injNeutralM n

injNeutralM :: Neutral' n -> Thawer n (Neutral' (S n))
injNeutralM (NFree ty name) =
  NFree
    <$> injValueM ty
    <*> pure (forLocal name (XName . EvLocal . There))
injNeutralM (NApp ty l r) =
  NApp <$> injValueM ty <*> injNeutralM l <*> injValueM r
injNeutralM (NProjField ty e a) =
  NProjField <$> injValueM ty <*> injNeutralM e <*> pure a
injNeutralM (NSplit sinfo scrut ln rn b) =
  NSplit
    <$> injSInfo sinfo
    <*> injNeutralM scrut
    <*> pure ln
    <*> pure rn
    <*> injBinder2 b
injNeutralM (NCase cinfo scrut b) =
  NCase
    <$> injCInfo cinfo
    <*> injNeutralM scrut
    <*> mapM injBinderM b

injCInfo :: CaseTypeInfo n -> Thawer n (CaseTypeInfo (S n))
injCInfo cinfo = do
  caseRetTy <- injValueM $ cinfo ^. #caseRetTy
  caseAltArgs <- mapM injValueM (cinfo ^. #caseAltArgs)
  pure CaseTypeInfo {..}

injSInfo :: SplitTypeInfo n -> Thawer n (SplitTypeInfo (S n))
injSInfo sinfo = do
  splitFstType <- injValueM $ sinfo ^. #splitFstType
  splitSndType <- injBinderM $ sinfo ^. #splitSndType
  splitRetType <- injValueM $ sinfo ^. #splitRetType
  pure SplitTypeInfo {..}

injBindTypeInfo :: BinderTypeSpec n -> Thawer n (BinderTypeSpec (S n))
injBindTypeInfo binfo = do
  argType <- injValueM $ binfo ^. #argType
  bodyType <- injBinderM $ binfo ^. #bodyType
  pure BinderTypeSpec {..}

injBinder :: (Value' n -> Value' n) -> Value' (S n) -> Value' (S n)
injBinder = flip runReader ThawEnv {curLvl = 0} . injBinderM

injBinderM :: (Value' n -> Value' n) -> Thawer n (Value' (S n) -> Value' (S n))
injBinderM f = asks $ \e -> injValueWith e . f . withEnv e . projValueM

injBinder2 :: (Value' n -> Value' n -> Value' n) -> Thawer n (Value' (S n) -> Value' (S n) -> Value' (S n))
injBinder2 f = asks $ \e l r ->
  injValueWith e $
    f (withEnv e $ projValueM l) (withEnv e $ projValueM r)

projValueM :: Value' (S n) -> Thawer n (Value' n)
projValueM VStar = pure VStar
projValueM (VPi an argTy body) = VPi an <$> projValueM argTy <*> projBinder body
projValueM (VSigma an argTy body) = VSigma an <$> projValueM argTy <*> projBinder body
projValueM (VPair bs an argTy body) =
  VPair <$> projBindTypeInfo bs <*> pure an <*> projValueM argTy <*> projValueM body
projValueM (VLam ty n b) = do
  VLam
    <$> projBindTypeInfo ty
    <*> pure n
    <*> projBinder b
projValueM (VRecord flds) = VRecord <$> mapM projValueM flds
projValueM (VMkRecord fldTys flds) =
  VMkRecord <$> mapM projValueM fldTys <*> mapM projValueM flds
projValueM (VVariant alts) = VVariant <$> mapM projValueM alts
projValueM (VInj alts tag x) =
  VInj <$> mapM projValueM alts <*> pure tag <*> projValueM x
projValueM (VNeutral n) = VNeutral <$> projNeutral n

projNeutral :: Neutral' (S n) -> Thawer n (Neutral' n)
projNeutral (NFree ty name) =
  NFree <$> projValueM ty <*> thawName name
projNeutral (NApp ty l r) =
  NApp <$> projValueM ty <*> projNeutral l <*> projValueM r
projNeutral (NProjField ty e a) =
  NProjField <$> projValueM ty <*> projNeutral e <*> pure a
projNeutral (NSplit sinfo scrut ln rn b) =
  NSplit
    <$> projSInfo sinfo
    <*> projNeutral scrut
    <*> pure ln
    <*> pure rn
    <*> projBinder2 b
projNeutral (NCase cinfo scrut b) =
  NCase
    <$> projCInfo cinfo
    <*> projNeutral scrut
    <*> mapM projBinder b

projCInfo :: CaseTypeInfo (S n) -> Thawer n (CaseTypeInfo n)
projCInfo cinfo = do
  caseRetTy <- projValueM $ cinfo ^. #caseRetTy
  caseAltArgs <- mapM projValueM (cinfo ^. #caseAltArgs)
  pure CaseTypeInfo {..}

projBindTypeInfo :: BinderTypeSpec (S n) -> Thawer n (BinderTypeSpec n)
projBindTypeInfo binfo = do
  argType <- projValueM $ binfo ^. #argType
  bodyType <- projBinder $ binfo ^. #bodyType
  pure BinderTypeSpec {..}

projSInfo :: SplitTypeInfo (S n) -> Thawer n (SplitTypeInfo n)
projSInfo sinfo = do
  splitFstType <- projValueM $ sinfo ^. #splitFstType
  splitSndType <- projBinder $ sinfo ^. #splitSndType
  splitRetType <- projValueM $ sinfo ^. #splitRetType
  pure SplitTypeInfo {..}

projBinder :: (Value' (S n) -> Value' (S n)) -> Thawer n (Value' n -> Value' n)
projBinder b = asks $ \e -> dimap (injValueWith e) (withEnv e . projValueM) b

projBinder2 :: (Value' (S n) -> Value' (S n) -> Value' (S n)) -> Thawer n (Value' n -> Value' n -> Value' n)
projBinder2 f = asks $ \e l r ->
  withEnv e $ projValueM $ f (injValueWith e l) (injValueWith e r)

substBound :: (HasCallStack) => Int -> Value' n -> Type' n -> Value' n
substBound i v (VLam lamTy mv f) =
  VLam (substBoundBinderSpec i v lamTy) mv $ substBound i v . f
substBound _ _ VStar = VStar
substBound i v (VPi mv va f) =
  VPi mv (substBound i v va) $ substBound i v . f
substBound i v (VSigma mv va f) =
  VSigma mv (substBound i v va) $ substBound i v . f
substBound i v (VPair ty mv l r) =
  VPair (substBoundBinderSpec i v ty) mv (substBound i v l) (substBound i v r)
substBound i v (VNeutral neu) =
  either VNeutral (substBound i v) $ substBoundNeutral i v neu
substBound i v (VRecord flds) = VRecord $ fmap (substBound i v) flds
substBound i v (VMkRecord fldTy flds) = VMkRecord (substBound i v <$> fldTy) $ substBound i v <$> flds
substBound i v (VVariant flds) = VVariant $ fmap (substBound i v) flds
substBound i v (VInj alts l e) = VInj (substBound i v <$> alts) l $ substBound i v e

substBoundBinderSpec :: Int -> Value' n -> BinderTypeSpec n -> BinderTypeSpec n
substBoundBinderSpec i v l =
  BinderTypeSpec
    { argType = substBound i v $ argType l
    , bodyType = substBound i v . bodyType l
    }

substBoundNeutral :: (HasCallStack) => Int -> Value' n -> Neutral' n -> Either (Neutral' n) (Value' n)
substBoundNeutral i v (NFree _ (Bound _ j)) | i == j = Right v
substBoundNeutral i v (NFree ty name) =
  Left $ NFree (substBound i v ty) name
substBoundNeutral i v (NApp retTy0 neu' va) =
  let va' = substBound i v va
      retTy = substBound i v retTy0
   in Bi.bimap (\vf' -> NApp retTy vf' va) (@@ va') $
        substBoundNeutral i v neu'
substBoundNeutral i v (NProjField retTy0 r f) =
  let retTy = substBound i v retTy0
   in case substBoundNeutral i v r of
        Right rec -> Right $ evalProjField retTy f rec
        Left n -> Left $ NProjField retTy n f
substBoundNeutral i v (NSplit sty0 scrut2 l r e) =
  let sty = substBoundSplitTy i v sty0
   in case substBoundNeutral i v scrut2 of
        Left scrut2' -> Left $ NSplit sty scrut2' l r $ \x y ->
          substBound i v $ e x y
        Right scrut2' -> Right $ evalSplit sty scrut2' l r e
substBoundNeutral i v (NCase caseTy0 e valts) =
  let caseTy = substBoundCaseTy i v caseTy0
   in case substBoundNeutral i v e of
        Left e' -> Left $ NCase caseTy e' $ fmap (substBound i v .) valts
        Right e' -> Right $ evalCase caseTy e' valts

substBoundSplitTy :: Int -> Value' n -> SplitTypeInfo n -> SplitTypeInfo n
substBoundSplitTy i v sinfo =
  SplitTypeInfo
    { splitFstType = substBound i v $ splitFstType sinfo
    , splitSndType = substBound (i + 1) v . splitSndType sinfo . substBound i v
    , splitRetType = substBound i v $ splitRetType sinfo
    }

substBoundCaseTy :: Int -> Value' n -> CaseTypeInfo n -> CaseTypeInfo n
substBoundCaseTy i v cinfo =
  CaseTypeInfo
    { caseRetTy = substBound i v $ caseRetTy cinfo
    , caseAltArgs = substBound i v <$> caseAltArgs cinfo
    }

type Eval = Eval' Z

data Eval' (n :: Lvl) deriving (Show, Eq, Ord, Generic, Data)

data EvalVars n
  = Quote !Int
  | EvLocal !(Ordinal n)
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

instance VarLike (EvalVars n) where
  varName (EvLocal i) =
    pure $
      Just $
        "<<EvLocal: " <> T.pack (show i) <> ">>"
  varName (Quote i) = pure $ Just $ "<<Quote:" <> tshow i <> ">>"

type instance XName (Eval' n) = EvalVars n

type instance XGlobal (Eval' n) = NoExtField

type instance XBound (Eval' n) = NoExtField

type instance XPrimName (Eval' n) = NoExtField

type instance XAnn (Eval' n) = Type' n

type instance AnnLHS (Eval' n) = Expr (Eval' n)

type instance AnnRHS (Eval' n) = Expr (Eval' n)

type instance XStar (Eval' n) = NoExtField

type instance XVar (Eval' n) = Type' n

type instance XApp (Eval' n) = Type' n

type instance AppLHS (Eval' n) = Expr (Eval' n)

type instance AppRHS (Eval' n) = Expr (Eval' n)

type instance XLam (Eval' n) = BinderTypeSpec n

data BinderTypeSpec n = BinderTypeSpec
  { argType :: !(Type' n)
  , bodyType :: !(Type' n -> Type' n)
  }
  deriving (Generic)

instance Show (BinderTypeSpec n) where
  showsPrec _ spc =
    let (arg, bdy) = lamTypeSpecRank spc
     in showString "BinderTypeSpec { "
          . showString "argType = "
          . shows arg
          . showString ", "
          . showString "bodyType = "
          . shows bdy
          . showString " }"

instance Eq (BinderTypeSpec n) where
  (==) = (==) `on` lamTypeSpecRank

instance Ord (BinderTypeSpec n) where
  compare = comparing lamTypeSpecRank

lamTypeSpecRank :: BinderTypeSpec n -> (Type' n, Type' n)
lamTypeSpecRank l =
  (argType l, VPi Anonymous (argType l) $ bodyType l)

type instance LamBindName (Eval' n) = AlphaName

type instance LamBindType (Eval' n) = Expr (Eval' n)

type instance LamBody (Eval' n) = Expr (Eval' n)

type instance XPi (Eval' n) = NoExtField

type instance PiVarName (Eval' n) = AlphaName

type instance PiVarType (Eval' n) = Expr (Eval' n)

type instance PiRHS (Eval' n) = Expr (Eval' n)

type instance XSigma (Eval' n) = NoExtField

type instance SigmaVarName (Eval' n) = AlphaName

type instance SigmaVarType (Eval' n) = Expr (Eval' n)

type instance SigmaBody (Eval' n) = Expr (Eval' n)

type instance XLam (Eval' n) = BinderTypeSpec n

type instance XPair (Eval' n) = BinderTypeSpec n

type instance PairFst (Eval' n) = Expr (Eval' n)

type instance PairSnd (Eval' n) = Expr (Eval' n)

type instance XSplit (Eval' n) = SplitTypeInfo n

type instance SplitScrutinee (Eval' n) = Expr (Eval' n)

type instance SplitFstName (Eval' n) = AlphaName

type instance SplitSndName (Eval' n) = AlphaName

type instance SplitBody (Eval' n) = Expr (Eval' n)

type instance XLet (Eval' n) = Type' n

type instance LetName (Eval' n) = AlphaName

type instance LetRHS (Eval' n) = Expr (Eval' n)

type instance LetBody (Eval' n) = Expr (Eval' n)

type instance XRecord (Eval' n) = NoExtField

type instance RecordFieldType (Eval' n) = Expr (Eval' n)

type instance XProjField (Eval' n) = Type' n

type instance ProjFieldRecord (Eval' n) = Expr (Eval' n)

type instance XMkRecord (Eval' n) = HashMap Text (Type' n)

type instance RecordField (Eval' n) = Expr (Eval' n)

type instance XOpen (Eval' n) = Type' n

type instance OpenRecord (Eval' n) = Expr (Eval' n)

type instance OpenBody (Eval' n) = Expr (Eval' n)

type instance XVariant (Eval' n) = NoExtField

type instance VariantArgType (Eval' n) = Expr (Eval' n)

type instance XInj (Eval' n) = HashMap Text (Type' n)

type instance InjArg (Eval' n) = Expr (Eval' n)

data CaseTypeInfo n = CaseTypeInfo
  { caseRetTy :: Type' n
  , caseAltArgs :: HM.HashMap Text (Type' n)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

type instance XCase (Eval' n) = CaseTypeInfo n

type instance CaseArg (Eval' n) = Expr (Eval' n)

type instance XCaseAlt (Eval' n) = NoExtField

type instance CaseAltVarName (Eval' n) = AlphaName

type instance CaseAltBody (Eval' n) = Expr (Eval' n)

type instance XExpr (Eval' n) = NoExtCon

instance Show (Neutral' n) where
  show = show . quoteNeutral 0
