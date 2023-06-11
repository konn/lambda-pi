{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Lambda.Syntax.LambdaPi.TreesThatGrow.Typing (
  -- * Conversion from Renamed AST
  toInferable,
  toCheckable,

  -- * Type checking and inference
  Context,
  Env (..),
  Value (..),
  Type,
  typeCheck,
  typeInfer,
  eval,
) where

import Control.Applicative ((<|>))
import Control.Lens hiding (Context)
import Control.Monad (unless)
import Data.Bifunctor qualified as Bi
import Data.DList.DNonEmpty qualified as DLNE
import Data.Either.Validation
import Data.Foldable (sequenceA_, traverse_)
import Data.Function (fix)
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.List
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe
import Data.Semialign.Indexed
import Data.Semigroup.Generic
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Text qualified as T
import Data.These (These (..))
import GHC.Generics (Generic)
import Language.Lambda.Syntax.LambdaPi.TreesThatGrow

toInferable :: Expr Rename -> Maybe (Expr Inferable)
toInferable = \case
  Ann NoExtField l r -> Ann NoExtField <$> toCheckable l <*> toCheckable r
  Star NoExtField -> pure $ Star NoExtField
  App NoExtField l r -> App NoExtField <$> toInferable l <*> toCheckable r
  Var NoExtField v -> pure $ Var NoExtField v
  Lam NoExtField v minType body -> do
    Lam NoExtField v <$> (toCheckable =<< minType) <*> toInferable body
  Pi NoExtField mv srcTy dstTy ->
    Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Nat NoExtField -> pure $ Nat NoExtField
  Zero NoExtField -> pure $ Zero NoExtField
  Succ NoExtField x -> Succ NoExtField <$> toCheckable x
  NatElim NoExtField t base step n ->
    NatElim NoExtField <$> toCheckable t <*> toCheckable base <*> toCheckable step <*> toCheckable n
  Vec NoExtField a n -> Vec NoExtField <$> toCheckable a <*> toCheckable n
  Nil NoExtField a -> Nil NoExtField <$> toCheckable a
  Cons NoExtField a n x xs ->
    Cons NoExtField <$> toCheckable a <*> toCheckable n <*> toCheckable x <*> toCheckable xs
  VecElim NoExtField x t base step n xs ->
    VecElim NoExtField
      <$> toCheckable x
      <*> toCheckable t
      <*> toCheckable base
      <*> toCheckable step
      <*> toCheckable n
      <*> toCheckable xs
  Record NoExtField (RecordFieldTypes flds) ->
    Record NoExtField . RecordFieldTypes <$> mapM (mapM toCheckable) flds
  MkRecord NoExtField (MkRecordFields flds) ->
    MkRecord NoExtField . MkRecordFields <$> mapM (mapM toInferable) flds
  ProjField NoExtField e fld -> flip (ProjField NoExtField) fld <$> toInferable e
  XExpr x -> noExtCon x

inf :: Expr Inferable -> Expr Checkable
inf = XExpr . Inf

toCheckable :: Expr Rename -> Maybe (Expr Checkable)
toCheckable = \case
  Ann NoExtField l r -> fmap inf . Ann NoExtField <$> toCheckable l <*> toCheckable r
  Star NoExtField -> pure $ inf $ Star NoExtField
  App NoExtField l r -> fmap inf . App NoExtField <$> toInferable l <*> toCheckable r
  Var NoExtField v -> pure $ inf $ Var NoExtField v
  Lam NoExtField mv (Just ty) body ->
    do
      fmap inf . Lam NoExtField mv <$> toCheckable ty <*> toInferable body
      <|> Lam NoExtField mv . Just <$> toCheckable ty <*> toCheckable body
  Lam NoExtField mv Nothing body -> do
    Lam NoExtField mv Nothing <$> toCheckable body
  Pi NoExtField mv srcTy dstTy ->
    fmap inf . Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Nat NoExtField -> pure $ inf $ Nat NoExtField
  Zero NoExtField -> pure $ inf $ Zero NoExtField
  Succ NoExtField x -> inf . Succ NoExtField <$> toCheckable x
  NatElim NoExtField t base step n ->
    fmap (fmap $ fmap inf) . NatElim NoExtField <$> toCheckable t <*> toCheckable base <*> toCheckable step <*> toCheckable n
  Vec NoExtField a n -> fmap inf . Vec NoExtField <$> toCheckable a <*> toCheckable n
  Nil NoExtField a -> inf . Nil NoExtField <$> toCheckable a
  Cons NoExtField a n x xs ->
    fmap (fmap $ fmap inf) . Cons NoExtField <$> toCheckable a <*> toCheckable n <*> toCheckable x <*> toCheckable xs
  VecElim NoExtField x t base step n xs ->
    fmap (fmap $ fmap $ fmap $ fmap inf) . VecElim NoExtField
      <$> toCheckable x
      <*> toCheckable t
      <*> toCheckable base
      <*> toCheckable step
      <*> toCheckable n
      <*> toCheckable xs
  Record NoExtField (RecordFieldTypes flds) ->
    inf . Record NoExtField . RecordFieldTypes <$> mapM (mapM toCheckable) flds
  MkRecord NoExtField (MkRecordFields flds) ->
    MkRecord NoExtField . MkRecordFields <$> mapM (mapM toCheckable) flds
      <|> inf . MkRecord NoExtField . MkRecordFields <$> mapM (mapM toInferable) flds
  ProjField NoExtField e fld -> inf . flip (ProjField NoExtField) fld <$> toInferable e
  XExpr x -> noExtCon x

data Value
  = VLam (Maybe Text) (Value -> Value)
  | VStar
  | VNat
  | VZero
  | VSucc Value
  | VPi (Maybe Text) Value (Value -> Value)
  | VNeutral Neutral
  | VVec Value Value
  | --  | VVariant (HashMap Text Value)
    VRecord (HashMap Text Value)
  | VMkRecord (HashMap Text Value)
  | VNil Value
  | VCons Value Value Value Value
  deriving (Generic)

instance Show Value where
  show = show . pprint . quote 0

data Neutral
  = NFree Name
  | NApp Neutral Value
  | NNatElim Value Value Value Neutral
  | NVecElim Value Value Value Value Value Neutral
  | NProjField Neutral Text
  deriving (Generic)

vfree :: Name -> Value
vfree = VNeutral . NFree

data Env = Env
  { namedBinds :: !(HM.HashMap Text Value)
  , localBinds :: !(Seq Value)
  }
  deriving ({- Show, -} Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid Env

type Type = Value

type Context = HashMap Name (Maybe Value, Type)

type Result = Either String

toEvalContext :: Context -> Env
toEvalContext ctx =
  mempty
    & #namedBinds
      .~ HM.fromList [(a, v) | (Global a, (Just v, _)) <- HM.toList ctx]

typeCheck :: Int -> Context -> Expr Checkable -> Type -> Result ()
typeCheck i ctx (XExpr (Inf e)) v = do
  v' <- typeInfer i ctx e
  let expect = quote 0 v
      actual = quote 0 v'
  unless (expect == actual) $
    Left $
      "Type mismatch: (expected, actual) = "
        <> show (pprint expect, pprint actual)
typeCheck i ctx (MkRecord NoExtField (MkRecordFields flds)) (VRecord flds') =
  -- TODO: Consider structural subtyping
  Bi.first (("Checking record expression failed: " <>) . unlines . DLNE.toList) $
    validationToEither $
      sequenceA_ $
        ialignWith
          ( \fld -> \case
              These f v ->
                Bi.first
                  (DLNE.singleton . (("Field `" <> T.unpack fld <> "'") <>))
                  $ eitherToValidation
                  $ typeCheck i ctx f v
              This {} ->
                Failure $
                  DLNE.singleton $
                    "The field `" <> T.unpack fld <> "' occurs in a record expression, but present in the expected type"
              That {} ->
                Failure $
                  DLNE.singleton $
                    "The field `" <> T.unpack fld <> "' occurs in expected type, but expression doesn't have it"
          )
          (HM.fromList flds)
          flds'
typeCheck _ _ mkRec@MkRecord {} ty =
  Left $
    "Expected a term of type `"
      <> show (pprint (quote 0 ty))
      <> "', but got a record: "
      <> show (pprint mkRec)
typeCheck _ _ (ProjField c _ _) _ = noExtCon c
typeCheck i ctx (Lam NoExtField _ _ e) (VPi _ ty ty') = do
  typeCheck
    (i + 1)
    (HM.insert (Local i) (Nothing, ty) ctx)
    (subst 0 (Var NoExtField (Local i)) e)
    $ ty'
    $ vfree
    $ Local i
typeCheck _ _ lam@(Lam NoExtField _ _ _) ty =
  Left $
    "Expected a tem of type `'"
      <> show (quote 0 ty)
      <> "', but got a lambda: "
      <> show (pprint lam)
typeCheck _ _ (Ann c _ _) _ = noExtCon c
typeCheck _ _ (Star c) _ = noExtCon c
typeCheck _ _ (Var c _) _ = noExtCon c
typeCheck _ _ (Pi c _ _ _) _ = noExtCon c
typeCheck _ _ (Nat c) _ = noExtCon c
typeCheck _ _ (Zero c) _ = noExtCon c
typeCheck _ _ (Succ c _) _ = noExtCon c
typeCheck _ _ (App c _ _) _ = noExtCon c
typeCheck _ _ (NatElim c _ _ _ _) _ = noExtCon c
typeCheck _ _ (Vec c _ _) _ = noExtCon c
typeCheck _ _ (Nil c _) _ = noExtCon c
typeCheck _ _ (Cons c _ _ _ _) _ = noExtCon c
typeCheck _ _ (VecElim c _ _ _ _ _ _) _ = noExtCon c
typeCheck _ _ (Record c _) _ = noExtCon c

typeInfer :: Int -> Context -> Expr Inferable -> Result Type
typeInfer !i ctx (Ann _ e rho) = do
  typeCheck i ctx rho VStar
  let !t = eval (toEvalContext ctx) rho
  typeCheck i ctx e t
  pure t
typeInfer _ _ Star {} = pure VStar
typeInfer _ ctx (Var _ x) = case HM.lookup x ctx of
  Just (_, t) -> pure t
  Nothing -> Left $ "Unknown identifier: " <> show x
typeInfer _ _ (XExpr (BVar bd)) = Left $ "Impossible: the type-checker encounters a bound variable: " <> show bd
typeInfer !i ctx (App NoExtField e e') = do
  let ctx' = toEvalContext ctx
  typeInfer i ctx e >>= \case
    VPi _ t t' -> do
      typeCheck i ctx e' t
      pure $ t' $ eval ctx' e'
    ty ->
      Left $
        "LHS of application must be has a function type, but got: "
          <> show (pprint e, pprint $ quote 0 ty)
typeInfer i ctx (Lam NoExtField _ ty body) = do
  let ctx' = toEvalContext ctx
  typeCheck i ctx ty VStar
  let tyVal = eval ctx' ty
  bodyTy <-
    typeInfer (i + 1) (HM.insert (Local i) (Nothing, tyVal) ctx) $
      subst 0 (Var NoExtField (Local i)) body
  pure $
    VPi Nothing tyVal $ \v ->
      substLocal i v bodyTy
typeInfer i ctx (Pi NoExtField _ rho rho') = do
  typeCheck i ctx rho VStar
  let ctx' = toEvalContext ctx
      t = eval ctx' rho
  typeCheck
    (i + 1)
    (HM.insert (Local i) (Nothing, t) ctx)
    (subst 0 (Var NoExtField (Local i)) rho')
    VStar
  pure VStar
typeInfer _ _ Nat {} = pure VStar
typeInfer _ _ Zero {} = pure VNat
typeInfer i ctx (Succ NoExtField k) = VNat <$ typeCheck i ctx k VNat
typeInfer i ctx (NatElim NoExtField m mz ms k) = do
  typeCheck i ctx m $ VPi (Just "k") VNat $ const VStar
  let mVal = eval (toEvalContext ctx) m
  typeCheck i ctx mz $ mVal @@ VZero
  typeCheck i ctx ms $
    VPi (Just "l") VNat $ \l ->
      VPi Nothing (mVal @@ l) $ const $ mVal @@ VSucc l
  typeCheck i ctx k VNat
  let kVal = eval (toEvalContext ctx) k
  pure $ mVal @@ kVal
typeInfer i ctx (Vec NoExtField a k) =
  VStar <$ typeCheck i ctx a VStar <* typeCheck i ctx k VNat
typeInfer i ctx (Nil NoExtField a) =
  VVec (eval (toEvalContext ctx) a) VZero <$ typeCheck i ctx a VStar
typeInfer i ctx (Cons NoExtField a n x xs) = do
  let ctx' = toEvalContext ctx
      aVal = eval ctx' a
      nVal = eval ctx' n
  typeCheck i ctx n VNat
  typeCheck i ctx a VStar
  typeCheck i ctx x aVal
  typeCheck i ctx xs $ VVec aVal nVal
  pure $ VVec aVal $ VSucc nVal
typeInfer i ctx (VecElim NoExtField a m mnil mcons n vs) = do
  let ctx' = toEvalContext ctx
  typeCheck i ctx a VStar
  let aVal = eval ctx' a
  typeCheck i ctx m $
    VPi (Just "k") VNat $ \k ->
      VPi Nothing (VVec aVal k) $ const VStar
  let mVal = eval ctx' m
  typeCheck i ctx mnil $
    vapps [mVal, VZero, VNil aVal]
  typeCheck i ctx mcons $
    VPi (Just "k") VNat $ \k ->
      VPi (Just "y") aVal $ \y ->
        VPi (Just "ys") (VVec aVal k) $ \ys ->
          VPi Nothing (vapps [mVal, k, ys]) $
            const $
              vapps [mVal, VSucc k, VCons aVal k y ys]
  typeCheck i ctx n VNat
  let nVal = eval ctx' n
  typeCheck i ctx vs $ VVec aVal nVal
  let vsVal = eval ctx' vs
  pure $ vapps [mVal, nVal, vsVal]
typeInfer i ctx (Record NoExtField flds) =
  VStar
    <$ traverse_ (flip (typeCheck i ctx) VStar . snd) (recFieldTypes flds)
typeInfer i ctx (MkRecord NoExtField (MkRecordFields flds)) = do
  VMkRecord . HM.fromList
    <$> traverse (traverse (typeInfer i ctx)) flds
typeInfer !i ctx (ProjField NoExtField e f) = do
  typeInfer i ctx e >>= \case
    VRecord flds ->
      case HM.lookup f flds of
        Just ty -> pure ty
        Nothing ->
          Left $
            "Record doesn't have the required field `"
              <> T.unpack f
              <> "': "
              <> show (map fst $ toOrderedList flds)
    ty ->
      Left $
        "LHS of record projection must be record, but got: "
          <> show (e, quote 0 ty)

subst :: forall m. KnownTypingMode m => Int -> Expr Inferable -> Expr (Typing m) -> Expr (Typing m)
subst !i r (Ann c e ty) = Ann c (subst i r e) (subst i r ty)
subst !_ _ (Star c) = Star c
subst !_ _ f@Var {} = f
subst !i r (App e f g) = App e (subst i r f) (subst i r g)
subst !i r (Lam x mv ann body) =
  case typingModeVal @m of
    SCheck -> Lam x mv (subst i r <$> ann) $ subst (i + 1) r body
    SInfer -> Lam x mv (subst i r ann) $ subst (i + 1) r body
subst !i r (Pi c mv ann body) =
  Pi c mv (subst i r ann) (subst (i + 1) r body)
subst _ _ (Nat c) = Nat c
subst _ _ (Zero c) = Zero c
subst i r (Succ c n) = Succ c $ subst i r n
subst i r (NatElim c t b ih n) =
  NatElim c (subst i r t) (subst i r b) (subst i r ih) (subst i r n)
subst i r (Vec c a n) = Vec c (subst i r a) (subst i r n)
subst i r (Nil c a) = Nil c $ subst i r a
subst i r (Cons c a n x xs) =
  Cons c (subst i r a) (subst i r n) (subst i r x) (subst i r xs)
subst i r (VecElim c a t b ih n xs) =
  VecElim c (subst i r a) (subst i r t) (subst i r b) (subst i r ih) (subst i r n) (subst i r xs)
subst i r (Record c (RecordFieldTypes flds)) =
  Record c $ RecordFieldTypes $ map (fmap (subst i r)) flds
subst i r (MkRecord c (MkRecordFields flds)) =
  case typingModeVal @m of
    SCheck -> MkRecord c $ MkRecordFields $ map (fmap (subst i r)) flds
    SInfer -> MkRecord c $ MkRecordFields $ map (fmap (subst i r)) flds
subst i r (ProjField c e f) =
  ProjField c (subst i r e) f
subst !i r bd@(XExpr (BVar j))
  | i == j = fromInferable r
  | otherwise = bd
subst !i r (XExpr (Inf e)) = XExpr $ Inf $ subst i r e

fromInferable :: forall m. KnownTypingMode m => Expr Inferable -> Expr (Typing m)
fromInferable =
  case typingModeVal @m of
    SInfer -> id
    SCheck -> inf

{-
subst i r (Lam NoExtField t e) =
  case typingModeVal @m of
    SInfer -> Lam NoExtField (subst i r t) $ subst (i + 1) r e
    SCheck -> Lam NoExtField (subst i r <$> t) $ subst (i + 1) r e
 -}

substLocal :: Int -> Value -> Type -> Value
substLocal i v (VLam mv f) = VLam mv $ substLocal i v . f
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
-- substLocal i v (VVariant vars) = VVariant $ fmap (substLocal i v) vars
substLocal i v (VRecord flds) = VRecord $ fmap (substLocal i v) flds
substLocal i v (VMkRecord flds) = VMkRecord $ fmap (substLocal i v) flds

substLocalNeutral :: Int -> Value -> Neutral -> Either Neutral Value
substLocalNeutral i v (NFree (Local j))
  | i == j = Right v
substLocalNeutral _ _ neu@NFree {} = Left neu
substLocalNeutral i v (NApp neu' va) =
  let va' = substLocal i v va
   in Bi.bimap (`NApp` va') (@@ va') $
        substLocalNeutral i v neu'
substLocalNeutral i v (NNatElim f f0 fsucc neuK) =
  let f' = substLocal i v f
      f0' = substLocal i v f0
      fsucc' = substLocal i v fsucc
   in Bi.bimap (NNatElim f' f0' fsucc') (evalNatElim f' f0' fsucc') $
        substLocalNeutral i v neuK
substLocalNeutral i v (NVecElim a f fnil fcons k kv) =
  let aVal = substLocal i v a
      fVal = substLocal i v f
      fnilVal = substLocal i v fnil
      fconsVal = substLocal i v fcons
      kVal = substLocal i v k
   in Bi.bimap
        (NVecElim aVal fVal fnilVal fconsVal kVal)
        (evalVecElim aVal fVal fnilVal fconsVal kVal)
        $ substLocalNeutral i v kv
substLocalNeutral i v (NProjField r f) =
  case substLocalNeutral i v r of
    Right rec -> Right $ evalProjField f rec
    Left n -> Left $ NProjField n f

quote :: Int -> Value -> Expr Checkable
quote i (VLam mv f) = Lam NoExtField mv Nothing $ quote (i + 1) $ f $ vfree $ Quote i
quote _ VStar = inf $ Star NoExtField
quote _ VNat = inf $ Nat NoExtField
quote _ VZero = inf $ Zero NoExtField
quote i (VSucc k) = inf $ Succ NoExtField $ quote i k
quote i (VVec a n) = inf $ Vec NoExtField (quote i a) (quote i n)
quote i (VNil a) = inf $ Nil NoExtField (quote i a)
quote i (VCons a n x xs) =
  inf $
    Cons
      NoExtField
      (quote i a)
      (quote i n)
      (quote i x)
      (quote i xs)
quote i (VPi mv v f) =
  inf $
    Pi NoExtField mv (quote i v) $
      quote (i + 1) $
        f $
          vfree $
            Quote i
quote i (VNeutral n) = inf $ quoteNeutral i n
-- quote i (VVariant vars) = Inf $ Variant $ toOrderedList $ fmap (quote i) vars
quote i (VRecord flds) =
  inf $
    Record NoExtField $
      RecordFieldTypes $
        HM.toList $
          fmap (quote i) flds
quote i (VMkRecord flds) =
  MkRecord NoExtField $ MkRecordFields $ HM.toList $ fmap (quote i) flds

quoteNeutral :: Int -> Neutral -> Expr Inferable
quoteNeutral i (NFree x) = boundFree i x
quoteNeutral i (NApp n v) = App NoExtField (quoteNeutral i n) (quote i v)
quoteNeutral i (NNatElim m mz ms k) =
  NatElim NoExtField (quote i m) (quote i mz) (quote i ms) $
    inf $
      quoteNeutral i k
quoteNeutral i (NVecElim a m mz ms k xs) =
  VecElim NoExtField (quote i a) (quote i m) (quote i mz) (quote i ms) (quote i k) $
    inf $
      quoteNeutral i xs
quoteNeutral i (NProjField r f) =
  ProjField NoExtField (quoteNeutral i r) f

boundFree :: Int -> Name -> Expr Inferable
boundFree i (Quote k) = XExpr $ BVar $ i - k - 1
boundFree _ x = Var NoExtField x

eval :: KnownTypingMode m => Env -> Expr (Typing m) -> Value
eval ctx (Ann _ e _) = eval ctx e
eval _ Star {} = VStar
eval ctx (Var _ fv) =
  case fv of
    Global g | Just v <- ctx ^. #namedBinds . at g -> v
    _ -> vfree fv
eval ctx (XExpr (BVar n)) = ctx ^?! #localBinds . ix n
eval ctx (App _ f x) = eval ctx f @@ eval ctx x
eval ctx (Lam _ mv _ e) = VLam mv $ \x ->
  eval
    (ctx & #localBinds %~ (x <|))
    e
eval ctx (Pi _ mv t t') =
  VPi mv (eval ctx t) $ \x -> eval (ctx & #localBinds %~ (x <|)) t'
eval _ Nat {} = VNat
eval _ Zero {} = VZero
eval ctx (Succ _ k) = VSucc $ eval ctx k
eval ctx (NatElim _ m mz ms k) =
  evalNatElim (eval ctx m) (eval ctx mz) (eval ctx ms) (eval ctx k)
eval ctx (Vec _ a n) = VVec (eval ctx a) (eval ctx n)
eval ctx (Nil _ a) = VNil $ eval ctx a
eval ctx (Cons _ a k v vk) =
  VCons (eval ctx a) (eval ctx k) (eval ctx v) (eval ctx vk)
eval ctx (VecElim _ a m mnil mcons k vk) =
  evalVecElim (eval ctx a) (eval ctx m) (eval ctx mnil) (eval ctx mcons) (eval ctx k) (eval ctx vk)
eval ctx (Record _ flds) = VRecord $ HM.fromList $ map (Bi.second $ eval ctx) $ recFieldTypes flds
eval ctx (MkRecord _ recs) =
  VRecord $ HM.fromList $ map (Bi.second $ eval ctx) $ mkRecFields recs
eval ctx (ProjField _ e f) = evalProjField f $ eval ctx e
eval ctx (XExpr (Inf e)) = eval ctx e

evalNatElim :: Value -> Value -> Value -> Value -> Value
evalNatElim mVal mzVal msVal = fix $ \recur kVal ->
  case kVal of
    VZero -> mzVal
    VSucc l -> msVal @@ l @@ recur l
    VNeutral nk ->
      VNeutral $
        NNatElim mVal mzVal msVal nk
    _ -> error "internal: eval natElim failed!"

evalVecElim :: Value -> Value -> Value -> Value -> Value -> Value -> Value
evalVecElim aVal mVal mnilVal mconsVal =
  fix $ \recur kVal xsVal ->
    case xsVal of
      VNil _ -> mnilVal
      VCons _ l x xs -> vapps [mconsVal, l, x, xs, recur l xs]
      VNeutral n ->
        VNeutral $ NVecElim aVal mVal mnilVal mconsVal kVal n
      _ -> error "Impossible: non-evaluatable VecElim case."

evalProjField :: Text -> Value -> Value
evalProjField f =
  \case
    VMkRecord flds ->
      fromMaybe
        ( error $
            "Impossible: given record doesn't have a field `"
              <> T.unpack f
              <> "': "
              <> show (sort $ HM.keys flds)
        )
        $ HM.lookup f flds
    VNeutral n -> VNeutral $ NProjField n f
    v ->
      error $
        "Impossible: non-evaulable record field projection: "
          <> show (f, quote 0 v)

infixl 9 @@

(@@) :: Value -> Value -> Value
VLam _ f @@ r = f r
VNeutral neu @@ r = VNeutral (NApp neu r)
l @@ r = error $ "Could not apply: " <> show (quote 0 l, quote 0 r)

vapps :: NonEmpty Type -> Type
vapps = foldl1 (@@)

toOrderedList :: HashMap Text a -> [(Text, a)]
toOrderedList = sortOn fst . HM.toList
