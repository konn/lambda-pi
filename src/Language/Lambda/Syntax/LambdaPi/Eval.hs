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
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Lambda.Syntax.LambdaPi.Eval (
  -- * Type checking and inference
  Env (..),
  Value (..),
  (@@),
  Type,
  Neutral (..),
  eval,
  unsubstBVar,
  unsubstBVarVal,
  LambdaTypeSpec (..),
  EvalVars (..),
  vapps,
  vfree,
  nSucc,
  nZero,
  vSucc,
  vZero,

  -- * ASTs
  quote,
  Eval,
  CaseTypeInfo (..),
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

data Value
  = VLam LambdaTypeSpec AlphaName (Value -> Value)
  | VStar
  | VPi AlphaName Value (Value -> Value)
  | VVec Value Value
  | VNil Value
  | VCons Value Value Value Value
  | VRecord (HashMap Text Value)
  | VMkRecord (HashMap Text Type) (HashMap Text Value)
  | VVariant (HashMap Text Value)
  | VInj (HashMap Text Type) Text Value
  | VNeutral Neutral
  deriving (Generic)

instance NFData LambdaTypeSpec where
  rnf LambdaTypeSpec {..} = rnf lamArgType `seq` rnfTyFun lamArgType lamBodyType

rnfTyFun :: Type -> (Type -> Type) -> ()
rnfTyFun argTy f = f `seq` f (vfree argTy (XName $ EvLocal 0)) `seq` ()

instance NFData Value where
  rnf (VLam lts a b) = lts `deepseq` a `deepseq` rnfTyFun (lamArgType lts) b
  rnf (VPi an a b) = an `deepseq` a `deepseq` rnfTyFun a b
  rnf VStar = ()
  rnf (VVec a n) = a `deepseq` rnf n
  rnf (VNil a) = rnf a
  rnf (VCons a n x xs) = a `deepseq` n `deepseq` x `deepseq` rnf xs
  rnf (VRecord flds) = rnf flds
  rnf (VMkRecord fldTys flds) = fldTys `deepseq` rnf flds
  rnf (VVariant tags) = rnf tags
  rnf (VInj alts l tag) = alts `deepseq` l `deepseq` rnf tag
  rnf (VNeutral n) = rnf n

typeOf :: Value -> Type
typeOf (VLam LambdaTypeSpec {..} x _) = VPi x lamArgType lamBodyType
typeOf VStar = VStar
typeOf VPi {} = VStar
typeOf VVec {} = VStar
typeOf (VNil a) = VVec a vZero
typeOf (VCons a n _ _) = VVec a (VNeutral nSucc @@ n)
typeOf VRecord {} = VStar
typeOf (VMkRecord fldTys _) = VRecord fldTys
typeOf VVariant {} = VStar
typeOf (VInj tags _ _) = VVariant tags
typeOf (VNeutral n) = typeOfNeutral n

nSucc :: Neutral
nSucc = NFree (VPi Anonymous VNat (const VNat)) (PrimName NoExtField Succ)

pattern VNat :: Value
pattern VNat = VNeutral (NFree VStar (PrimName NoExtField Nat))

vSucc :: Value
vSucc = VNeutral nSucc

nZero :: Neutral
nZero = NFree VNat $ PrimName NoExtField Zero

vZero :: Value
vZero = VNeutral $ NFree VNat $ PrimName NoExtField Zero

instance Show Value where
  show = show . pprint . quote 0

instance Pretty e (Expr Eval) => Pretty e Value where
  pretty = pretty . quote 0

data Neutral
  = NFree Type (Name Eval)
  | NApp Type Neutral Value
  | NVecElim Type Value Value Value Value Value Neutral
  | NProjField Type Neutral Text
  | NCase CaseTypeInfo Neutral (HM.HashMap Text (Value -> Value))
  -- FIXME: Work out what NOpen should be
  deriving (Generic)

instance NFData Neutral where
  rnf (NFree ty n) = ty `deepseq` rnf n
  rnf (NApp ty l r) = ty `deepseq` l `deepseq` rnf r
  rnf (NVecElim ty a t b i n xs) =
    ty `deepseq` a `deepseq` t `deepseq` b `deepseq` i `deepseq` n `deepseq` rnf xs
  rnf (NProjField ty p l) = ty `deepseq` p `deepseq` rnf l
  rnf (NCase ty e xs) = ty `deepseq` e `deepseq` rnf (fmap (rnfTyFun VStar) xs)

nPrim :: Type -> Prim -> Neutral
nPrim ty p = NFree ty $ PrimName NoExtField p

inferPrim :: HasCallStack => Prim -> Type
inferPrim Tt = VNeutral $ nPrim VStar Unit
inferPrim Unit = VStar
inferPrim Nat = VStar
inferPrim Zero = VNat
inferPrim Succ = VPi Anonymous VNat (const VNat)
inferPrim NatElim = natElimType

typeOfNeutral :: Neutral -> Type
typeOfNeutral (NFree retTy _) = retTy
typeOfNeutral (NApp retTy _ _) = retTy
typeOfNeutral (NVecElim retTy _ _ _ _ _ _) = retTy
typeOfNeutral (NProjField retTy _ _) = retTy
typeOfNeutral (NCase CaseTypeInfo {..} _ _) = caseRetTy

vfree :: Type -> Name Eval -> Value
vfree = fmap VNeutral . NFree

data Env = Env
  { namedBinds :: !(HM.HashMap Text Value)
  , boundValues :: ![Value]
  }
  deriving (Show, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid Env

instance Eq Value where
  (==) = (==) `on` quote 0

instance Ord Value where
  compare = comparing $ quote 0

type Type = Value

quote :: Int -> Value -> Expr Eval
quote i (VLam ls@LambdaTypeSpec {..} mv f) =
  Lam ls mv (quote i lamArgType) $
    quote (i + 1) $
      f $
        vfree lamArgType $
          XName $
            Quote i
quote _ VStar = Star NoExtField
quote i (VVec a n) = Vec NoExtField (quote i a) (quote i n)
quote i (VNil a) = Nil NoExtField (quote i a)
quote i (VCons a n x xs) =
  Cons NoExtField (quote i a) (quote i n) (quote i x) (quote i xs)
quote i (VPi mv v f) =
  Pi NoExtField mv (quote i v) $
    quote (i + 1) $
      f $
        vfree v $
          XName $
            Quote i
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

quoteNeutral :: Int -> Neutral -> Expr Eval
quoteNeutral i (NFree ty x) = boundFree ty i x
quoteNeutral i (NApp ty n v) = App ty (quoteNeutral i n) (quote i v)
quoteNeutral i (NVecElim ty a m mz ms k xs) =
  VecElim ty (quote i a) (quote i m) (quote i mz) (quote i ms) (quote i k) $
    quoteNeutral i xs
quoteNeutral i (NProjField ty r f) =
  ProjField ty (quoteNeutral i r) f
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

boundFree :: Type -> Int -> Name Eval -> Expr Eval
boundFree ty i (XName (Quote k)) = Var ty $ Bound NoExtField $ i - k - 1
boundFree ty _ x = Var ty x

eval :: HasCallStack => Env -> Expr Eval -> Value
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
eval ctx (Let _ _ e b) =
  eval
    (ctx & #boundValues %~ (eval ctx e <|))
    b
eval ctx (Vec _ a n) = VVec (eval ctx a) (eval ctx n)
eval ctx (Nil _ a) = VNil $ eval ctx a
eval ctx (Cons _ a k v vk) =
  VCons (eval ctx a) (eval ctx k) (eval ctx v) (eval ctx vk)
eval ctx (VecElim ty a m mnil mcons k vk) =
  evalVecElim ty (eval ctx a) (eval ctx m) (eval ctx mnil) (eval ctx mcons) (eval ctx k) (eval ctx vk)
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
eval ctx (Case cinfo e (CaseAlts alts)) =
  evalCase cinfo (eval ctx e) $
    HM.fromList alts <&> \(CaseAlt _ _ b) v ->
      eval (ctx & #boundValues %~ (v <|)) b
eval _ (XExpr c) = noExtCon c

evalCase :: CaseTypeInfo -> Value -> HashMap Text (Value -> Value) -> Value
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

evalNatElim :: Value -> Value -> Value -> Value -> Value
evalNatElim t t0 tStep = fix $ \recur kVal ->
  case kVal of
    VNeutral (NFree _ (PrimName _ Zero)) -> t0
    VNeutral (NApp _ (NFree _ (PrimName _ Succ)) l) -> tStep @@ l @@ recur l
    VNeutral nk ->
      ( vfree natElimType (PrimName NoExtField NatElim)
          @@ t
          @@ t0
          @@ tStep
      )
        @@ VNeutral nk
    _ -> error "internal: eval natElim failed!"

natElimType :: HasCallStack => Type
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

evalVecElim :: Type -> Value -> Value -> Value -> Value -> Value -> Value -> Value
evalVecElim retTy aVal mVal mnilVal mconsVal =
  fix $ \recur kVal xsVal ->
    case xsVal of
      VNil _ -> mnilVal
      VCons _ l x xs -> vapps [mconsVal, l, x, xs, recur l xs]
      VNeutral n ->
        VNeutral $ NVecElim retTy aVal mVal mnilVal mconsVal kVal n
      _ -> error "Impossible: non-evaluatable VecElim case."

evalProjField :: Type -> Text -> Value -> Value
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

pattern (:@) :: Neutral -> Value -> Neutral
pattern l :@ r <- NApp _ l r

pattern P :: Prim -> Neutral
pattern P p <- NFree _ (PrimName _ p)

(@@) :: HasCallStack => Value -> Value -> Value
VLam _ _ f @@ r = f r
VNeutral (P NatElim :@ t :@ base :@ ind) @@ n = evalNatElim t base ind n
VNeutral neu @@ r
  | VPi _ _ f <- typeOfNeutral neu =
      VNeutral $ NApp (f r) neu r
l @@ r = error $ "Could not apply: " <> show ((pprint l, typeOf l), (pprint r, typeOf r))

vapps :: NonEmpty Type -> Type
vapps = foldl1 (@@)

unsubstBVarVal :: Int -> Value -> Value
unsubstBVarVal = fmap (`runReader` 0) . unsubstBVarValM

unsubstBVar :: Int -> Expr Eval -> Expr Eval
unsubstBVar i = flip runReader 0 . go
  where
    go (Var ty name) = do
      -- NOTE: This isn't needed if occurs check passed
      Var <$> unsubstBVarValM i ty <*> case name of
        XName (EvLocal j)
          | j == i -> asks $ Bound NoExtField
        _ -> pure name
    go (Pi NoExtField mn l r) =
      Pi NoExtField mn <$> go l <*> local (+ 1) (go r)
    go (Lam lamTy mn l r) =
      Lam
        <$> unsubstLamTy i lamTy
        <*> pure mn
        <*> go l
        <*> local (+ 1) (go r)
    go (Ann e l r) = Ann <$> unsubstBVarValM i e <*> go l <*> go r
    go (App e l r) = App <$> unsubstBVarValM i e <*> go l <*> go r
    go (Let c mn e v) =
      Let <$> unsubstBVarValM i c <*> pure mn <*> go e <*> local (+ 1) (go v)
    go s@Star {} = pure s
    go (Vec NoExtField x n) =
      Vec NoExtField <$> go x <*> go n
    go (Nil NoExtField c) = Nil NoExtField <$> go c
    go (Cons NoExtField ty n x xs) =
      Cons NoExtField
        <$> go ty
        <*> go n
        <*> go x
        <*> go xs
    go (VecElim ty x t tNil tCons n xs) =
      VecElim
        <$> unsubstBVarValM i ty
        <*> go x
        <*> go t
        <*> go tNil
        <*> go tCons
        <*> go n
        <*> go xs
    go (Record NoExtField (RecordFieldTypes flds)) =
      Record NoExtField . RecordFieldTypes <$> mapM (mapM go) flds
    go (MkRecord tys (MkRecordFields flds)) =
      MkRecord
        <$> mapM (unsubstBVarValM i) tys
        <*> (MkRecordFields <$> mapM (mapM go) flds)
    go (ProjField ty e l) =
      ProjField <$> unsubstBVarValM i ty <*> go e <*> pure l
    go (Open ty r b) =
      Open <$> unsubstBVarValM i ty <*> go r <*> go b
    go (Variant NoExtField (VariantTags flds)) =
      Variant NoExtField . VariantTags <$> mapM (mapM go) flds
    go (Inj tags l p) =
      Inj <$> mapM (unsubstBVarValM i) tags <*> pure l <*> go p
    go (Case caseTy e (CaseAlts alts)) =
      Case
        <$> unsubstBVarCaseInfo i caseTy
        <*> go e
        <*> (CaseAlts <$> local (+ 1) (mapM (mapM goAlt) alts))
    go (XExpr c) = noExtCon c
    goAlt (CaseAlt NoExtField name a) =
      CaseAlt NoExtField name <$> go a

unsubstBVarCaseInfo :: Int -> CaseTypeInfo -> Reader Int CaseTypeInfo
unsubstBVarCaseInfo i CaseTypeInfo {..} =
  CaseTypeInfo
    <$> unsubstBVarValM i caseRetTy
    <*> mapM (unsubstBVarValM i) caseAltArgs

unsubstLamTy :: Int -> LambdaTypeSpec -> Reader Int LambdaTypeSpec
unsubstLamTy i LambdaTypeSpec {..} = do
  lvl <- ask
  LambdaTypeSpec
    <$> unsubstBVarValM i lamArgType
    <*> pure (flip runReader (lvl + 1) . unsubstBVarValM i . lamBodyType)

unsubstBVarValToM :: Int -> Int -> Value -> Value
unsubstBVarValToM lvl i v = runReader (unsubstBVarValM i v) lvl

unsubstBVarValM :: Int -> Value -> Reader Int Value
unsubstBVarValM i = go
  where
    go VStar = pure VStar
    go (VPi mv argTy f) = do
      lvl <- ask
      VPi mv
        <$> unsubstBVarValM i argTy
        <*> pure (unsubstBVarValToM (lvl + 1) i . f)
    go (VLam lt name f) = do
      lvl <- ask
      VLam
        <$> unsubstLamTy i lt
        <*> pure name
        <*> pure (unsubstBVarValToM (lvl + 1) i . f)
    go (VVec a n) = VVec <$> go a <*> go n
    go (VNil ty) = VNil <$> go ty
    go (VCons a n x xs) =
      VCons <$> go a <*> go n <*> go x <*> go xs
    go (VRecord flds) = VRecord <$> mapM go flds
    go (VMkRecord fldTys flds) =
      VMkRecord <$> mapM go fldTys <*> mapM go flds
    go (VVariant tags) = VVariant <$> mapM go tags
    go (VInj alts l v) = VInj <$> mapM go alts <*> pure l <*> go v
    go (VNeutral n) = VNeutral <$> unsubstBoundNeutral i n

unsubstBoundNeutral :: Int -> Neutral -> Reader Int Neutral
unsubstBoundNeutral i = go
  where
    go (NFree ty v) =
      NFree
        <$> unsubstBVarValM i ty
        <*> case v of
          XName (EvLocal j)
            | j == i -> asks $ Bound NoExtField
          _ -> pure v
    go (NApp ty l v) =
      NApp
        <$> unsubstBVarValM i ty
        <*> go l
        <*> unsubstBVarValM i v
    go (NVecElim ty x t t0 tsucc n xs) =
      NVecElim
        <$> unsubstBVarValM i ty
        <*> unsubstBVarValM i x
        <*> unsubstBVarValM i t
        <*> unsubstBVarValM i t0
        <*> unsubstBVarValM i tsucc
        <*> unsubstBVarValM i n
        <*> go xs
    go (NProjField ty p l) =
      NProjField <$> unsubstBVarValM i ty <*> go p <*> pure l
    go (NCase ty scr alts) = do
      lvl <- ask
      NCase
        <$> unsubstBVarCaseInfo i ty
        <*> go scr
        <*> pure
          ( fmap
              ((flip runReader lvl . unsubstBVarValM i) .)
              alts
          )

substBound :: HasCallStack => Int -> Value -> Type -> Value
substBound i v (VLam lamTy mv f) =
  VLam (substBoundLamSpec i v lamTy) mv $ substBound i v . f
substBound _ _ VStar = VStar
substBound i v (VPi mv va f) =
  VPi mv (substBound i v va) $ substBound i v . f
substBound i v (VNeutral neu) =
  either VNeutral (substBound i v) $ substBoundNeutral i v neu
substBound i v (VVec va va') = VVec (substBound i v va) (substBound i v va')
substBound i v (VNil va) = VNil $ substBound i v va
substBound i v (VCons va va' va2 va3) =
  VCons (substBound i v va) (substBound i v va') (substBound i v va2) (substBound i v va3)
substBound i v (VRecord flds) = VRecord $ fmap (substBound i v) flds
substBound i v (VMkRecord fldTy flds) = VMkRecord (substBound i v <$> fldTy) $ substBound i v <$> flds
substBound i v (VVariant flds) = VVariant $ fmap (substBound i v) flds
substBound i v (VInj alts l e) = VInj (substBound i v <$> alts) l $ substBound i v e

substBoundLamSpec :: Int -> Value -> LambdaTypeSpec -> LambdaTypeSpec
substBoundLamSpec i v l =
  LambdaTypeSpec
    { lamArgType = substBound i v $ lamArgType l
    , lamBodyType = substBound i v . lamBodyType l
    }

substBoundNeutral :: HasCallStack => Int -> Value -> Neutral -> Either Neutral Value
substBoundNeutral i v (NFree _ (Bound _ j)) | i == j = Right v
substBoundNeutral i v (NFree ty name) =
  Left $ NFree (substBound i v ty) name
substBoundNeutral i v (NApp retTy0 neu' va) =
  let va' = substBound i v va
      retTy = substBound i v retTy0
   in Bi.bimap (\vf' -> NApp retTy vf' va) (@@ va') $
        substBoundNeutral i v neu'
substBoundNeutral i v (NVecElim retTy0 a f fnil fcons k kv) =
  let aVal = substBound i v a
      fVal = substBound i v f
      fnilVal = substBound i v fnil
      fconsVal = substBound i v fcons
      kVal = substBound i v k
      retTy = substBound i v retTy0
   in Bi.bimap
        (NVecElim retTy aVal fVal fnilVal fconsVal kVal)
        (evalVecElim retTy aVal fVal fnilVal fconsVal kVal)
        $ substBoundNeutral i v kv
substBoundNeutral i v (NProjField retTy0 r f) =
  let retTy = substBound i v retTy0
   in case substBoundNeutral i v r of
        Right rec -> Right $ evalProjField retTy f rec
        Left n -> Left $ NProjField retTy n f
substBoundNeutral i v (NCase caseTy0 e valts) =
  let caseTy = substBoundCaseTy i v caseTy0
   in case substBoundNeutral i v e of
        Left e' -> Left $ NCase caseTy e' $ fmap (substBound i v .) valts
        Right e' -> Right $ evalCase caseTy e' valts

substBoundCaseTy :: Int -> Value -> CaseTypeInfo -> CaseTypeInfo
substBoundCaseTy i v cinfo =
  CaseTypeInfo
    { caseRetTy = substBound i v $ caseRetTy cinfo
    , caseAltArgs = substBound i v <$> caseAltArgs cinfo
    }

data Eval deriving (Show, Eq, Ord, Generic, Data)

data EvalVars
  = Quote !Int
  | EvLocal !Int
  deriving (Show, Eq, Ord, Generic, Data)
  deriving anyclass (NFData)

instance VarLike EvalVars where
  varName (EvLocal i) =
    pure $
      Just $
        "<<EvLocal: " <> T.pack (show i) <> ">>"
  varName (Quote i) = pure $ Just $ "<<Quote:" <> tshow i <> ">>"

type instance XName Eval = EvalVars

type instance XGlobal Eval = NoExtField

type instance XBound Eval = NoExtField

type instance XPrimName Eval = NoExtField

type instance XAnn Eval = Type

type instance AnnLHS Eval = Expr Eval

type instance AnnRHS Eval = Expr Eval

type instance XStar Eval = NoExtField

type instance XVar Eval = Type

type instance XApp Eval = Type

type instance AppLHS Eval = Expr Eval

type instance AppRHS Eval = Expr Eval

type instance XLam Eval = LambdaTypeSpec

data LambdaTypeSpec = LambdaTypeSpec
  { lamArgType :: !Type
  , lamBodyType :: !(Type -> Type)
  }
  deriving (Generic)

instance Show LambdaTypeSpec where
  showsPrec _ spc =
    let (arg, bdy) = lamTypeSpecRank spc
     in showString "LambdaTypeSpec { "
          . showString "lamArgType = "
          . shows arg
          . showString ", "
          . showString "lamBodyType = "
          . shows bdy
          . showString " }"

instance Eq LambdaTypeSpec where
  (==) = (==) `on` lamTypeSpecRank

instance Ord LambdaTypeSpec where
  compare = comparing lamTypeSpecRank

lamTypeSpecRank :: LambdaTypeSpec -> (Type, Type)
lamTypeSpecRank l =
  (lamArgType l, VPi Anonymous (lamArgType l) $ lamBodyType l)

type instance LamBindName Eval = AlphaName

type instance LamBindType Eval = Expr Eval

type instance LamBody Eval = Expr Eval

type instance XPi Eval = NoExtField

type instance PiVarName Eval = AlphaName

type instance PiVarType Eval = Expr Eval

type instance PiRHS Eval = Expr Eval

type instance XLet Eval = Type

type instance LetName Eval = AlphaName

type instance LetRHS Eval = Expr Eval

type instance LetBody Eval = Expr Eval

type instance XVec Eval = NoExtField

type instance VecType Eval = Expr Eval

type instance VecLength Eval = Expr Eval

type instance XNil Eval = NoExtField

type instance NilType Eval = Expr Eval

type instance XCons Eval = NoExtField

type instance ConsType Eval = Expr Eval

type instance ConsLength Eval = Expr Eval

type instance ConsHead Eval = Expr Eval

type instance ConsTail Eval = Expr Eval

type instance XVecElim Eval = Type

type instance VecElimEltType Eval = Expr Eval

type instance VecElimRetFamily Eval = Expr Eval

type instance VecElimBaseCase Eval = Expr Eval

type instance VecElimInductiveStep Eval = Expr Eval

type instance VecElimLength Eval = Expr Eval

type instance VecElimInput Eval = Expr Eval

type instance XRecord Eval = NoExtField

type instance RecordFieldType Eval = Expr Eval

type instance XProjField Eval = Type

type instance ProjFieldRecord Eval = Expr Eval

type instance XMkRecord Eval = HashMap Text Type

type instance RecordField Eval = Expr Eval

type instance XOpen Eval = Type

type instance OpenRecord Eval = Expr Eval

type instance OpenBody Eval = Expr Eval

type instance XVariant Eval = NoExtField

type instance VariantArgType Eval = Expr Eval

type instance XInj Eval = HashMap Text Type

type instance InjArg Eval = Expr Eval

data CaseTypeInfo = CaseTypeInfo
  { caseRetTy :: Type
  , caseAltArgs :: HM.HashMap Text Type
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (NFData)

type instance XCase Eval = CaseTypeInfo

type instance CaseArg Eval = Expr Eval

type instance XCaseAlt Eval = NoExtField

type instance CaseAltVarName Eval = AlphaName

type instance CaseAltBody Eval = Expr Eval

type instance XExpr Eval = NoExtCon

instance Show Neutral where
  show = show . quoteNeutral 0
