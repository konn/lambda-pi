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
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
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
  substLocal,
  LambdaTypeSpec (..),
  vapps,
  vfree,

  -- * ASTs
  quote,
  Eval,
  XExprEval (..),
  CaseTypeInfo (..),
) where

import Control.Lens hiding (Context)
import Data.Bifunctor qualified as Bi
import Data.Function (fix, on)
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.List
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe
import Data.Ord (comparing)
import Data.Semigroup.Generic
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi
import Text.PrettyPrint.Monadic (Pretty (..))
import Text.PrettyPrint.Monadic qualified as PP

data Value
  = VLam LambdaTypeSpec AlphaName (Value -> Value)
  | VStar
  | VNat
  | VZero
  | VSucc Value
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

typeOf :: Value -> Type
typeOf (VLam LambdaTypeSpec {..} x _) = VPi x lamArgType lamBodyType
typeOf VStar = VStar
typeOf VNat = VStar
typeOf VZero = VNat
typeOf VSucc {} = VPi Anonymous VNat (const VNat)
typeOf VPi {} = VStar
typeOf VVec {} = VStar
typeOf (VNil a) = VVec a VZero
typeOf (VCons a n _ _) = VVec a (VSucc n)
typeOf VRecord {} = VStar
typeOf (VMkRecord fldTys _) = VRecord fldTys
typeOf VVariant {} = VStar
typeOf (VInj tags _ _) = VVariant tags
typeOf (VNeutral n) = typeOfNeutral n

instance Show Value where
  show = show . pprint . quote 0

instance Pretty e (Expr Eval) => Pretty e Value where
  pretty = pretty . quote 0

data Neutral
  = NFree Type Name
  | NPrim Type Prim
  | NApp Type Neutral Value
  | NNatElim Type Value Value Value Neutral
  | NVecElim Type Value Value Value Value Value Neutral
  | NProjField Type Neutral Text
  | NCase CaseTypeInfo Neutral (HM.HashMap Text (Value -> Value))
  -- FIXME: Work out what NOpen should be
  deriving (Generic)

typeOfNeutral :: Neutral -> Type
typeOfNeutral (NFree retTy _) = retTy
typeOfNeutral (NPrim retTy _) = retTy
typeOfNeutral (NApp retTy _ _) = retTy
typeOfNeutral (NNatElim retTy _ _ _ _) = retTy
typeOfNeutral (NVecElim retTy _ _ _ _ _ _) = retTy
typeOfNeutral (NProjField retTy _ _) = retTy
typeOfNeutral (NCase CaseTypeInfo {..} _ _) = caseRetTy

vfree :: Type -> Name -> Value
vfree = fmap VNeutral . NFree

data Env = Env
  { namedBinds :: !(HM.HashMap Text Value)
  , localBinds :: !(Seq Value)
  }
  deriving ({- Show, -} Generic)
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
          Quote i
quote _ VStar = Star NoExtField
quote _ VNat = Nat NoExtField
quote _ VZero = Zero VNat
quote i (VSucc k) = Succ NoExtField $ quote i k
quote i (VVec a n) = Vec NoExtField (quote i a) (quote i n)
quote i (VNil a) = Nil NoExtField (quote i a)
quote i (VCons a n x xs) =
  Cons NoExtField (quote i a) (quote i n) (quote i x) (quote i xs)
quote i (VPi mv v f) =
  Pi NoExtField mv (quote i v) $
    quote (i + 1) $
      f $
        vfree VStar $
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
quoteNeutral i (NNatElim ty m mz ms k) =
  NatElim ty (quote i m) (quote i mz) (quote i ms) $
    quoteNeutral i k
quoteNeutral i (NVecElim ty a m mz ms k xs) =
  VecElim ty (quote i a) (quote i m) (quote i mz) (quote i ms) (quote i k) $
    quoteNeutral i xs
quoteNeutral i (NProjField ty r f) =
  ProjField ty (quoteNeutral i r) f
quoteNeutral _ (NPrim ty v) = Var ty $ PrimName v
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
                      Quote i
          )
          caseAltArgs
          alts

boundFree :: Type -> Int -> Name -> Expr Eval
boundFree ty i (Quote k) = XExpr $ BoundVar ty $ i - k - 1
boundFree ty _ x = Var ty x

eval :: Env -> Expr Eval -> Value
eval ctx (Ann _ e _) = eval ctx e
eval _ Star {} = VStar
eval ctx (Var ty fv) =
  case fv of
    PrimName p -> VNeutral $ NPrim ty p
    Global g | Just v <- ctx ^. #namedBinds . at g -> v
    _ -> vfree ty fv
eval ctx (XExpr (BoundVar _ n)) = ctx ^?! #localBinds . ix n
eval ctx (App _ f x) = eval ctx f @@ eval ctx x
eval ctx (Lam ty mv _ e) = VLam ty mv $ \x ->
  eval
    (ctx & #localBinds %~ (x <|))
    e
eval ctx (Pi _ mv t t') =
  VPi mv (eval ctx t) $ \x -> eval (ctx & #localBinds %~ (x <|)) t'
eval ctx (Let _ _ e b) =
  eval
    (ctx & #localBinds %~ (eval ctx e <|))
    b
eval _ Nat {} = VNat
eval _ Zero {} = VZero
eval ctx (Succ _ k) = VSucc $ eval ctx k
eval ctx (NatElim retTy m mz ms k) =
  evalNatElim retTy (eval ctx m) (eval ctx mz) (eval ctx ms) (eval ctx k)
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
    -- FIXME: Work out what NOpen should be
    {-
    VNeutral v -> ...
    VNeutralChk (Inf v) -> ...
    -}
    otr ->
      error $
        "Impossible: open requires a record, but got a term of type: "
          <> show (pprint $ quote 0 otr)
eval ctx (Variant _ flds) = VVariant $ HM.fromList $ map (Bi.second $ eval ctx) $ variantTags flds
eval ctx (Inj alts t e) = VInj alts t $ eval ctx e
eval ctx (Case cinfo e (CaseAlts alts)) =
  evalCase cinfo (eval ctx e) $
    HM.fromList alts <&> \(CaseAlt _ _ b) v ->
      eval (ctx & #localBinds %~ (v <|)) b

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

evalNatElim :: Type -> Value -> Value -> Value -> Value -> Value
evalNatElim retTy mVal mzVal msVal = fix $ \recur kVal ->
  case kVal of
    VZero -> mzVal
    VSucc l -> msVal @@ l @@ recur l
    VNeutral nk ->
      VNeutral $
        NNatElim retTy mVal mzVal msVal nk
    _ -> error "internal: eval natElim failed!"

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

infixl 9 @@

(@@) :: Value -> Value -> Value
VLam _ _ f @@ r = f r
VNeutral neu @@ r
  | VPi _ _ f <- typeOfNeutral neu =
      VNeutral $ NApp (f $ typeOf r) neu r
l @@ r = error $ "Could not apply: " <> show (pprint l, pprint r)

vapps :: NonEmpty Type -> Type
vapps = foldl1 (@@)

substLocal :: Int -> Value -> Type -> Value
substLocal i v (VLam lamTy mv f) = VLam (substLamSpec i v lamTy) mv $ substLocal i v . f
substLocal _ _ VStar = VStar
substLocal _ _ VNat = VNat
substLocal _ _ VZero = VZero
substLocal i v (VSucc va) = VSucc $ substLocal i v va
substLocal i v (VPi mv va f) =
  VPi mv (substLocal i v va) $ substLocal i v . f
substLocal i v (VNeutral neu) =
  either VNeutral id $ substLocalNeutral i v neu
substLocal i v (VVec va va') = VVec (substLocal i v va) (substLocal i v va')
substLocal i v (VNil va) = VNil $ substLocal i v va
substLocal i v (VCons va va' va2 va3) =
  VCons (substLocal i v va) (substLocal i v va') (substLocal i v va2) (substLocal i v va3)
substLocal i v (VRecord flds) = VRecord $ fmap (substLocal i v) flds
substLocal i v (VMkRecord fldTy flds) = VMkRecord (substLocal i v <$> fldTy) $ substLocal i v <$> flds
substLocal i v (VVariant flds) = VVariant $ fmap (substLocal i v) flds
substLocal i v (VInj alts l e) = VInj (substLocal i v <$> alts) l $ substLocal i v e

substLamSpec :: Int -> Value -> LambdaTypeSpec -> LambdaTypeSpec
substLamSpec i v l =
  LambdaTypeSpec
    { lamArgType = substLocal i v $ lamArgType l
    , lamBodyType = substLocal i v . lamBodyType l
    }

substLocalNeutral :: Int -> Value -> Neutral -> Either Neutral Value
substLocalNeutral i v (NFree _ (Local j))
  | i == j = Right v
substLocalNeutral _ _ neu@NFree {} = Left neu
substLocalNeutral i v (NApp retTy neu' va) =
  let va' = substLocal i v va
   in Bi.bimap (\vf' -> NApp retTy vf' va) (@@ va') $
        substLocalNeutral i v neu'
substLocalNeutral i v (NNatElim retTy f f0 fsucc neuK) =
  let f' = substLocal i v f
      f0' = substLocal i v f0
      fsucc' = substLocal i v fsucc
   in Bi.bimap (NNatElim retTy f' f0' fsucc') (evalNatElim retTy f' f0' fsucc') $
        substLocalNeutral i v neuK
substLocalNeutral i v (NVecElim retTy a f fnil fcons k kv) =
  let aVal = substLocal i v a
      fVal = substLocal i v f
      fnilVal = substLocal i v fnil
      fconsVal = substLocal i v fcons
      kVal = substLocal i v k
   in Bi.bimap
        (NVecElim retTy aVal fVal fnilVal fconsVal kVal)
        (evalVecElim retTy aVal fVal fnilVal fconsVal kVal)
        $ substLocalNeutral i v kv
substLocalNeutral i v (NProjField retTy r f) =
  case substLocalNeutral i v r of
    Right rec -> Right $ evalProjField retTy f rec
    Left n -> Left $ NProjField retTy n f
substLocalNeutral _ _ (NPrim retTy p) = Left $ NPrim retTy p
substLocalNeutral i v (NCase caseTy e valts) =
  case substLocalNeutral i v e of
    Left e' -> Left $ NCase caseTy e' $ fmap (substLocal i v .) valts
    Right e' -> Right $ evalCase caseTy e' valts

data Eval deriving (Show, Eq, Ord, Generic)

type instance XAnn Eval = Type

type instance AnnLHS Eval = Expr Eval

type instance AnnRHS Eval = Expr Eval

type instance XStar Eval = NoExtField

type instance XVar Eval = Type

type instance Id Eval = FreeVar Eval

type instance BoundVar Eval = Int

type instance FreeVar Eval = Name

type instance XApp Eval = Type

type instance AppLHS Eval = Expr Eval

type instance AppRHS Eval = Expr Eval

type instance XLam Eval = LambdaTypeSpec

data LambdaTypeSpec = LambdaTypeSpec
  { lamArgType :: Type
  , lamBodyType :: Type -> Type
  }
  deriving (Generic)

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

type instance XNat Eval = NoExtField

type instance XZero Eval = Type

type instance XSucc Eval = NoExtField

type instance SuccBody Eval = Expr Eval

type instance XNatElim Eval = Type

type instance NatElimRetFamily Eval = Expr Eval

type instance NatElimBaseCase Eval = Expr Eval

type instance NatElimInductionStep Eval = Expr Eval

type instance NatElimInput Eval = Expr Eval

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
  deriving (Eq, Ord, Generic)

type instance XCase Eval = CaseTypeInfo

type instance CaseArg Eval = Expr Eval

type instance XCaseAlt Eval = NoExtField

type instance CaseAltVarName Eval = AlphaName

type instance CaseAltBody Eval = Expr Eval

type instance XExpr Eval = XExprEval

data XExprEval = BoundVar !Type !Int
  deriving (Show, Eq, Ord, Generic)

instance Pretty PrettyEnv XExprEval where
  pretty (BoundVar _ i) = do
    mtn <- preview $ #boundVars . ix i
    case mtn of
      Just (t, n)
        | n > 0 -> PP.text t <> PP.char '_' <> PP.int n
        | otherwise -> PP.text t
      Nothing -> "<<Global:" <> pretty i <> ">>"
