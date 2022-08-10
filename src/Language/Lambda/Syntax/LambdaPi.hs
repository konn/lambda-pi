{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

{- | Implementation based on:

<A Tutorial Implementation of a Dependently Typed Lambda Calculus https://www.andres-loeh.de/LambdaPi/>
by Andres Löh, Conor McBride, and Wouter Swiestra.
-}
module Language.Lambda.Syntax.LambdaPi where

import Control.Arrow ((+++))
import Control.Lens (Ixed (ix), at, (%~), (.~), (^.), (^?!))
import Control.Monad (unless)
import Data.Function (fix, (&))
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)
import Data.List (foldl1')
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Semigroup.Generic (GenericSemigroupMonoid (..))
import Data.Sequence (Seq, (<|))
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Numeric.Natural (Natural)

data Mode = Inferable | Checkable
  deriving (Show, Eq, Ord, Generic)

data family Term (mode :: Mode)

data instance Term 'Inferable
  = Term 'Checkable ::: Term 'Checkable
  | Star
  | LamAnn (Term 'Checkable) (Term 'Inferable)
  | Pi (Term 'Checkable) (Term 'Checkable)
  | NatElim (Term 'Checkable) (Term 'Checkable) (Term 'Checkable) (Term 'Checkable)
  | Bound Int
  | Free Name
  | Term 'Inferable :@: Term 'Checkable
  | Nat
  | Zero
  | Succ (Term 'Checkable)
  | Vec (Term 'Checkable) (Term 'Checkable)
  | Nil (Term 'Checkable)
  | Cons (Term 'Checkable) (Term 'Checkable) (Term 'Checkable) (Term 'Checkable)
  | VecElim (Term 'Checkable) (Term 'Checkable) (Term 'Checkable) (Term 'Checkable) (Term 'Checkable) (Term 'Checkable)
  deriving (Show, Eq, Ord)

infixl 0 :::

infixl 9 :@:

data instance Term 'Checkable
  = Inf (Term 'Inferable)
  | Lam (Term 'Checkable)
  deriving (Show, Eq, Ord)

data Name = Global Text | Local Int | Quote Int
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (Hashable)

type Type = Value

data Value
  = VLam (Value -> Value)
  | VStar
  | VNat
  | VZero
  | VSucc Value
  | VPi Value (Value -> Value)
  | VNeutral Neutral
  | VVec Value Value
  | VNil Value
  | VCons Value Value Value Value
  deriving (Generic)

instance Show Value where
  showsPrec d val = prettyChkPrec 0 d $ quote 0 val

data Neutral
  = NFree Name
  | NApp Neutral Value
  | NNatElim Value Value Value Neutral
  | NVecElim Value Value Value Value Value Neutral
  deriving (Generic)

vfree :: Name -> Value
vfree = VNeutral . NFree

data Env = Env
  { namedBinds :: !(HM.HashMap Text Value)
  , localBinds :: !(Seq Value)
  }
  deriving (Show, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid Env

evalInf :: Env -> Term 'Inferable -> Value
evalInf ctx (e ::: _) = evalChk ctx e
evalInf ctx (LamAnn _ e) = VLam $ \x ->
  evalInf
    (ctx & #localBinds %~ (x <|))
    e
evalInf ctx (Bound n) = ctx ^?! #localBinds . ix n
evalInf ctx (Free (Global g))
  | Just v <- ctx ^. #namedBinds . at g = v
evalInf _ (Free n) = vfree n
evalInf ctx (f :@: x) = evalInf ctx f @@ evalChk ctx x
evalInf _ Star = VStar
evalInf ctx (Pi t t') = VPi (evalChk ctx t) $ \x -> evalChk (ctx & #localBinds %~ (x <|)) t'
evalInf _ Nat = VNat
evalInf _ Zero = VZero
evalInf ctx (Succ k) = VSucc $ evalChk ctx k
evalInf ctx (NatElim m mz ms k) =
  evalNatElim (evalChk ctx m) (evalChk ctx mz) (evalChk ctx ms) (evalChk ctx k)
evalInf ctx (Vec a n) = VVec (evalChk ctx a) (evalChk ctx n)
evalInf ctx (Nil a) = VNil $ evalChk ctx a
evalInf ctx (Cons a k v vk) =
  VCons
    (evalChk ctx a)
    (evalChk ctx k)
    (evalChk ctx v)
    (evalChk ctx vk)
evalInf ctx (VecElim a m mnil mcons k vk) =
  evalVecElim (evalChk ctx a) (evalChk ctx m) (evalChk ctx mnil) (evalChk ctx mcons) (evalChk ctx k) (evalChk ctx vk)

evalVecElim :: Value -> Value -> Value -> Value -> Value -> Value -> Value
evalVecElim aVal mVal mnilVal mconsVal =
  fix $ \recur kVal xsVal ->
    case xsVal of
      VNil _ -> mnilVal
      VCons _ l x xs -> vapps [mconsVal, l, x, xs, recur l xs]
      VNeutral n ->
        VNeutral $ NVecElim aVal mVal mnilVal mconsVal kVal n
      _ -> error "Impossible: non-evaluatable VecElim case."

evalNatElim :: Value -> Value -> Value -> Value -> Value
evalNatElim mVal mzVal msVal = fix $ \recur kVal ->
  case kVal of
    VZero -> mzVal
    VSucc l -> msVal @@ l @@ recur l
    VNeutral nk ->
      VNeutral $
        NNatElim mVal mzVal msVal nk
    _ -> error "internal: eval natElim failed!"

infixl 9 @@

(@@) :: Value -> Value -> Value
VLam f @@ r = f r
VNeutral neu @@ r = VNeutral (NApp neu r)
l @@ r = error $ "Could not apply: " <> show (quote 0 l, quote 0 r)

evalChk :: Env -> Term 'Checkable -> Value
evalChk ctx (Inf te) = evalInf ctx te
evalChk ctx (Lam e) = VLam $ \x -> evalChk (ctx & #localBinds %~ (x <|)) e

type Context = HashMap Name (Maybe Value, Type)

type Result = Either String

typeInfer :: Int -> Context -> Term 'Inferable -> Result Type
typeInfer !i ctx (e ::: rho) = do
  typeCheck i ctx rho VStar
  let !t =
        evalChk (toEvalContext ctx) rho
  typeCheck i ctx e t
  pure t
typeInfer _ _ Star = pure VStar
typeInfer _ _ Nat = pure VStar
typeInfer _ _ Zero = pure VNat
typeInfer i ctx (Succ k) = VNat <$ typeCheck i ctx k VNat
typeInfer i ctx (NatElim m mz ms k) = do
  typeCheck i ctx m $ VPi VNat $ const VStar
  let mVal = evalChk (toEvalContext ctx) m
  typeCheck i ctx mz $ mVal @@ VZero
  typeCheck i ctx ms $
    VPi VNat $ \l ->
      VPi (mVal @@ l) $ const $ mVal @@ VSucc l
  typeCheck i ctx k VNat
  let kVal = evalChk (toEvalContext ctx) k
  pure $ mVal @@ kVal
typeInfer i ctx (Vec a k) =
  VStar <$ typeCheck i ctx a VStar <* typeCheck i ctx k VNat
typeInfer i ctx (Nil a) =
  VVec (evalChk (toEvalContext ctx) a) VZero <$ typeCheck i ctx a VStar
typeInfer i ctx (Cons a n x xs) = do
  let ctx' = toEvalContext ctx
      aVal = evalChk ctx' a
      nVal = evalChk ctx' n
  typeCheck i ctx n VNat
  typeCheck i ctx a VStar
  typeCheck i ctx x aVal
  typeCheck i ctx xs $ VVec aVal nVal
  pure $ VVec aVal $ VSucc nVal
typeInfer i ctx (VecElim a m mnil mcons n vs) = do
  let ctx' = toEvalContext ctx
  typeCheck i ctx a VStar
  let aVal = evalChk ctx' a
  typeCheck i ctx m $
    VPi VNat $ \k ->
      VPi (VVec aVal k) $ const VStar
  let mVal = evalChk ctx' m
  typeCheck i ctx mnil $
    vapps [mVal, VZero, VNil aVal]
  typeCheck i ctx mcons $
    VPi VNat $ \k ->
      VPi aVal $ \y ->
        VPi (VVec aVal k) $ \ys ->
          VPi (vapps [mVal, k, ys]) $
            const $ vapps [mVal, VSucc k, VCons aVal k y ys]
  typeCheck i ctx n VNat
  let nVal = evalChk ctx' n
  typeCheck i ctx vs $ VVec aVal nVal
  let vsVal = evalChk ctx' vs
  pure $ vapps [mVal, nVal, vsVal]
typeInfer i ctx (LamAnn ty body) = do
  let ctx' = toEvalContext ctx
  typeCheck i ctx ty VStar
  let tyVal = evalChk ctx' ty
  bodyTy <-
    typeInfer (i + 1) (HM.insert (Local i) (Nothing, tyVal) ctx) $
      substInf 0 (Free (Local i)) body
  pure $
    VPi tyVal $ \v ->
      substLocal i v bodyTy
typeInfer _ ctx (Free x) = case HM.lookup x ctx of
  Just (_, t) -> pure t
  Nothing -> Left $ "Unknown identifier: " <> show x
typeInfer !i ctx (Pi rho rho') = do
  typeCheck i ctx rho VStar
  let ctx' = toEvalContext ctx
      t = evalChk ctx' rho
  typeCheck
    (i + 1)
    (HM.insert (Local i) (Nothing, t) ctx)
    (substChk 0 (Free (Local i)) rho')
    VStar
  pure VStar
typeInfer !i ctx (e :@: e') = do
  let ctx' = toEvalContext ctx
  typeInfer i ctx e >>= \case
    VPi t t' -> do
      typeCheck i ctx e' t
      pure $ t' $ evalChk ctx' e'
    ty ->
      Left $
        "LHS of application must be has a function type, but got: "
          <> show (e, quote 0 ty)
typeInfer _ _ bd@Bound {} =
  Left $ "Impossible: the type-checker encounters a bound variable: " <> show bd

toEvalContext :: Context -> Env
toEvalContext ctx =
  mempty & #namedBinds
    .~ HM.fromList [(a, v) | (Global a, (Just v, _)) <- HM.toList ctx]

vapps :: NonEmpty Type -> Type
vapps = foldl1' (@@) . NE.toList

typeCheck :: Int -> Context -> Term 'Checkable -> Type -> Result ()
typeCheck !i ctx (Inf e) v = do
  v' <- typeInfer i ctx e
  unless (quote 0 v == quote 0 v') $
    Left $
      "Type mismatch (inf); (term, expected, actual) = ("
        <> prettyInfPrec
          i
          10
          e
          ( showString ", " $
              prettyChkPrec i 10 (quote i v) $
                showString ", " $
                  prettyChkPrec i 10 (quote i v') ")"
          )
        <> "; in context: "
        <> show ctx
typeCheck !i ctx (Lam e) (VPi ty ty') = do
  typeCheck
    (i + 1)
    (HM.insert (Local i) (Nothing, ty) ctx)
    (substChk 0 (Free (Local i)) e)
    $ ty' $ vfree $ Local i
typeCheck _ _ e ty =
  Left $ "Type check failed: " <> show (e, quote 0 ty)

substInf :: Int -> Term 'Inferable -> Term 'Inferable -> Term 'Inferable
substInf !i r (e ::: ty) = substChk i r e ::: substChk i r ty
substInf i r (LamAnn t e) = LamAnn (substChk i r t) $ substInf (i + 1) r e
substInf _ _ Nat = Nat
substInf _ _ Zero = Zero
substInf i r (Succ k) = Succ $ substChk i r k
substInf i r (NatElim m mz ms k) =
  NatElim (substChk i r m) (substChk i r mz) (substChk i r ms) (substChk i r k)
substInf i r (Vec a n) = Vec (substChk i r a) (substChk i r n)
substInf i r (Nil a) = Nil (substChk i r a)
substInf i r (Cons a n x xs) =
  Cons (substChk i r a) (substChk i r n) (substChk i r x) (substChk i r xs)
substInf i r (VecElim a m mn mc k vk) =
  VecElim (substChk i r a) (substChk i r m) (substChk i r mn) (substChk i r mc) (substChk i r k) (substChk i r vk)
substInf _ _ Star = Star
substInf i r (Pi t t') = Pi (substChk i r t) (substChk (i + 1) r t')
substInf !i r bd@(Bound j)
  | i == j = r
  | otherwise = bd
substInf _ _ f@Free {} = f
substInf !i r (e :@: e') =
  substInf i r e :@: substChk i r e'

substChk :: Int -> Term 'Inferable -> Term 'Checkable -> Term 'Checkable
substChk !i r (Inf e) = Inf $ substInf i r e
substChk !i r (Lam e) = Lam $ substChk (i + 1) r e

substLocal :: Int -> Value -> Type -> Value
substLocal i v (VLam f) = VLam $ substLocal i v . f
substLocal _ _ VStar = VStar
substLocal _ _ VNat = VNat
substLocal _ _ VZero = VZero
substLocal i v (VSucc va) = VSucc $ substLocal i v va
substLocal i v (VPi va f) =
  VPi (substLocal i v va) $ substLocal i v . f
substLocal i v (VNeutral neu) =
  either VNeutral id $ substLocalNeutral i v neu
substLocal i v (VVec va va') = VVec (substLocal i v va) (substLocal i v va')
substLocal i v (VNil va) = VNil $ substLocal i v va
substLocal i v (VCons va va' va2 va3) =
  VCons (substLocal i v va) (substLocal i v va') (substLocal i v va2) (substLocal i v va3)

substLocalNeutral :: Int -> Value -> Neutral -> Either Neutral Value
substLocalNeutral i v (NFree (Local j))
  | i == j = Right v
substLocalNeutral _ _ neu@NFree {} = Left neu
substLocalNeutral i v (NApp neu' va) =
  let va' = substLocal i v va
   in (`NApp` va') +++ (@@ va') $
        substLocalNeutral i v neu'
substLocalNeutral i v (NNatElim f f0 fsucc neuK) =
  let f' = substLocal i v f
      f0' = substLocal i v f0
      fsucc' = substLocal i v fsucc
   in NNatElim f' f0' fsucc' +++ evalNatElim f' f0' fsucc' $
        substLocalNeutral i v neuK
substLocalNeutral i v (NVecElim a f fnil fcons k kv) =
  let aVal = substLocal i v a
      fVal = substLocal i v f
      fnilVal = substLocal i v fnil
      fconsVal = substLocal i v fcons
      kVal = substLocal i v k
   in NVecElim aVal fVal fnilVal fconsVal kVal
        +++ evalVecElim aVal fVal fnilVal fconsVal kVal
        $ substLocalNeutral i v kv

quote :: Int -> Value -> Term 'Checkable
quote i (VLam f) = Lam $ quote (i + 1) $ f $ vfree $ Quote i
quote _ VStar = Inf Star
quote _ VNat = Inf Nat
quote _ VZero = Inf Zero
quote i (VSucc k) = Inf $ Succ $ quote i k
quote i (VVec a n) = Inf $ Vec (quote i a) (quote i n)
quote i (VNil a) = Inf $ Nil (quote i a)
quote i (VCons a n x xs) = Inf $ Cons (quote i a) (quote i n) (quote i x) (quote i xs)
quote i (VPi v f) =
  Inf $ Pi (quote i v) $ quote (i + 1) $ f $ vfree $ Quote i
quote i (VNeutral n) = Inf $ quoteNeutral i n

quoteNeutral :: Int -> Neutral -> Term 'Inferable
quoteNeutral i (NFree x) = boundFree i x
quoteNeutral i (NApp n v) = quoteNeutral i n :@: quote i v
quoteNeutral i (NNatElim m mz ms k) =
  NatElim (quote i m) (quote i mz) (quote i ms) $
    Inf $ quoteNeutral i k
quoteNeutral i (NVecElim a m mz ms k xs) =
  VecElim (quote i a) (quote i m) (quote i mz) (quote i ms) (quote i k) $
    Inf $ quoteNeutral i xs

boundFree :: Int -> Name -> Term 'Inferable
boundFree i (Quote k) = Bound $ i - k - 1
boundFree _ x = Free x

pattern Pi' :: Term 'Checkable -> Term 'Checkable -> Term 'Checkable
pattern Pi' l r = Inf (Pi l r)

pattern Star' :: Term 'Checkable
pattern Star' = Inf Star

pattern Bound' :: Int -> Term 'Checkable
pattern Bound' i = Inf (Bound i)

pattern Free' :: Name -> Term 'Checkable
pattern Free' i = Inf (Free i)

id' :: Term 'Inferable
id' = Lam (Lam $ Bound' 0) ::: Pi' Star' (Pi' (Bound' 0) (Bound' 1))

typeEnv :: Context
typeEnv = HM.fromList [(Global "a", (Nothing, VStar)), (Global "x", (Nothing, vfree $ Global "a")), (Global "y", (Nothing, vfree $ Global "a"))]

pattern Nat' :: Term 'Checkable
pattern Nat' = Inf Nat

pattern Succ' :: Term 'Checkable -> Term 'Checkable
pattern Succ' n = Inf (Succ n)

pattern Zero' :: Term 'Checkable
pattern Zero' = Inf Zero

plus' :: Term 'Inferable
plus' =
  LamAnn
    Nat'
    ( NatElim
        (Lam $ Pi' Nat' Nat')
        (Lam $ Bound' 0)
        ( Lam $
            Lam $
              Lam $
                Succ' $ Inf $ Bound 1 :@: Bound' 0
        )
        (Bound' 0)
    )

pattern Cons' ::
  Term 'Checkable ->
  Term 'Checkable ->
  Term 'Checkable ->
  Term 'Checkable ->
  Term 'Checkable
pattern Cons' a b x xs = Inf (Cons a b x xs)

pattern Vec' :: Term 'Checkable -> Term 'Checkable -> Term 'Checkable
pattern Vec' a b = Inf (Vec a b)

type Level = Int

prettyInfPrec :: Level -> Int -> Term 'Inferable -> ShowS
prettyInfPrec lvl _ (te ::: te') =
  showParen True $
    prettyChkPrec lvl 11 te . showString " :: " . prettyChkPrec lvl 10 te'
prettyInfPrec _ _ Star = showString "*"
prettyInfPrec lvl d (LamAnn te te') =
  showParen (d > 4) $
    showString "λ(x_" . shows lvl . showString " : " . prettyChkPrec lvl d te
      . showString "). "
      . prettyInfPrec (lvl + 1) 4 te'
prettyInfPrec lvl d (Pi te te') =
  showParen (d > 4) $
    showString "Π(x_" . shows lvl
      . showString " : "
      . prettyChkPrec lvl 4 te
      . showString "). "
      . prettyChkPrec (lvl + 1) 4 te'
prettyInfPrec lvl d (NatElim te te' te2 te3) =
  showParen (d > 10) $
    showString "natElim"
      . showChar ' '
      . prettyChkPrec lvl 11 te
      . showChar ' '
      . prettyChkPrec lvl 11 te'
      . showChar ' '
      . prettyChkPrec lvl 11 te2
      . showChar ' '
      . prettyChkPrec lvl 11 te3
prettyInfPrec lvl _ (Bound n) =
  showString "x_" . shows (lvl - n - 1)
prettyInfPrec lvl _ (Free na) = prettyName lvl na
prettyInfPrec lvl d (te :@: te') =
  showParen (d > 10) $
    prettyInfPrec lvl 10 te . showChar ' '
      . prettyChkPrec lvl 11 te'
prettyInfPrec _ _ Nat = showString "ℕ"
prettyInfPrec _ _ Zero = showString "0"
prettyInfPrec lvl d sc@(Succ te) =
  case prettyAsNat sc of
    Just n -> shows n
    _ ->
      showParen (d > 10) $
        showString "succ " . prettyChkPrec lvl 11 te
prettyInfPrec lvl d (Vec te te') =
  showParen (d > 10) $
    showString "Vec " . prettyChkPrec lvl 11 te
      . showChar ' '
      . prettyChkPrec lvl 11 te'
prettyInfPrec lvl d (Nil te) =
  showParen (d > 10) $
    showString "nil " . prettyChkPrec lvl 11 te
prettyInfPrec lvl d (Cons te te' te2 te3) =
  showParen (d > 10) $
    showString "cons"
      . showChar ' '
      . prettyChkPrec lvl 11 te
      . showChar ' '
      . prettyChkPrec lvl 11 te'
      . showChar ' '
      . prettyChkPrec lvl 11 te2
      . showChar ' '
      . prettyChkPrec lvl 11 te3
prettyInfPrec lvl d (VecElim te te' te2 te3 te4 te5) =
  showParen (d > 10) $
    showString "vecElim"
      . showChar ' '
      . prettyChkPrec lvl 11 te
      . showChar ' '
      . prettyChkPrec lvl 11 te'
      . showChar ' '
      . prettyChkPrec lvl 11 te2
      . showChar ' '
      . prettyChkPrec lvl 11 te3
      . showChar ' '
      . prettyChkPrec lvl 11 te4
      . showChar ' '
      . prettyChkPrec lvl 11 te5

prettyAsNat :: Term 'Inferable -> Maybe Natural
prettyAsNat Zero = Just 0
prettyAsNat (Succ (Inf n)) = succ <$> prettyAsNat n
prettyAsNat _ = Nothing

prettyName :: Level -> Name -> ShowS
prettyName _ (Global s) = showString $ T.unpack s
prettyName lvl (Local n) = showString "x_" . shows (lvl - n - 1)
prettyName _ Quote {} = error "Could not happen!"

prettyChkPrec :: Level -> Int -> Term 'Checkable -> ShowS
prettyChkPrec lvl d (Inf te') = prettyInfPrec lvl d te'
prettyChkPrec lvl d (Lam te') =
  showParen (d > 4) $
    showString "λx_" . shows lvl . showString ". "
      . prettyChkPrec (lvl + 1) 4 te'

occursChk :: Int -> Term 'Checkable -> Bool
occursChk i (Inf te') = occursInf i te'
occursChk i (Lam te') = occursChk (i + 1) te'

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
  occursChk i te' || occursChk i te2 || occursChk i te3 || occursChk i te4
    || occursChk i te5
    || occursChk i te6

natElim' :: Term 'Inferable
natElim' =
  LamAnn (Pi' Nat' Star') $
    LamAnn (Inf $ Bound 0 :@: Zero') $
      LamAnn
        ( Pi'
            Nat'
            ( Pi'
                (Inf $ Bound 2 :@: Bound' 0)
                (Inf $ Bound 3 :@: Inf (Succ (Bound' 1)))
            )
        )
        $ LamAnn Nat' $
          NatElim (Bound' 3) (Bound' 2) (Bound' 1) (Bound' 0)

-- >>> typeInfer 0 mempty natElim
-- Right (Π(x_0 : Π(x_0 : ℕ). *). Π(x_1 : x_0 0). Π(x_2 : Π(x_2 : ℕ). Π(x_3 : x_0 x_2). x_0 (succ x_2)). Π(x_3 : ℕ). x_0 x_3)

vecElim' :: Term 'Inferable
vecElim' =
  LamAnn Star' $
    LamAnn (Pi' Nat' $ Pi' (Vec' (Bound' 1) (Bound' 0)) Star') $
      LamAnn
        (Inf $ Bound 0 :@: Zero' :@: Inf (Nil (Bound' 1)))
        $ LamAnn
          ( Pi' Nat' $
              Pi' (Bound' 3) $
                Pi' (Vec' (Bound' 4) (Bound' 1)) $
                  Pi' (Inf $ Bound 4 :@: Bound' 2 :@: Bound' 0) $
                    Inf $
                      Bound 5
                        :@: Succ' (Bound' 3)
                        :@: Cons' (Bound' 6) (Bound' 3) (Bound' 2) (Bound' 1)
          )
          $ LamAnn Nat' $
            LamAnn (Vec' (Bound' 4) (Bound' 0)) $
              VecElim (Bound' 5) (Bound' 4) (Bound' 3) (Bound' 2) (Bound' 1) (Bound' 0)

-- >>> typeInfer 0 mempty vecElim'
-- Right (Π(x_0 : *). Π(x_1 : Π(x_1 : ℕ). Π(x_2 : Vec x_0 x_1). *). Π(x_2 : x_1 0 (nil x_0)). Π(x_3 : Π(x_3 : ℕ). Π(x_4 : x_0). Π(x_5 : Vec x_0 x_3). Π(x_6 : x_1 x_3 x_5). x_1 (succ x_3) (cons x_0 x_3 x_4 x_5)). Π(x_4 : ℕ). Π(x_5 : Vec x_0 x_4). x_1 x_4 x_5)

vecCon' :: Term 'Inferable
vecCon' = LamAnn Star' $ LamAnn Nat' $ Vec (Bound' 1) (Bound' 0)

cons' :: Term 'Inferable
cons' =
  LamAnn
    Star'
    $ LamAnn Nat' $
      LamAnn (Bound' 1) $
        LamAnn (Vec' (Bound' 2) (Bound' 1)) $
          Cons (Bound' 3) (Bound' 2) (Bound' 1) (Bound' 0)

-- >>> typeInfer 0 mempty cons'
-- Right (Π(x_0 : *). Π(x_1 : ℕ). Π(x_2 : x_0). Π(x_3 : Vec x_0 x_1). Vec x_0 (succ x_1))

tryInferType :: Term 'Checkable -> Result Type
tryInferType (Inf te) = typeInfer 0 mempty te
tryInferType te@Lam {} =
  Left $
    "A type of a raw lambda cannot be inferred: "
      ++ prettyChkPrec 0 10 te ""

tryEval :: Term 'Checkable -> Result (Value, Type)
tryEval e = do
  !typ <- tryInferType e
  pure (evalChk mempty e, typ)

tryEvalAs :: Term 'Checkable -> Term 'Checkable -> Result Value
tryEvalAs e ty = do
  typeCheck 0 mempty ty VStar
  let tyVal = evalChk mempty ty
  typeCheck 0 mempty e tyVal
  pure $ evalChk mempty e

-- >>> cons'
-- LamAnn (Inf Star) (LamAnn (Inf Nat) (LamAnn (Inf (Bound 1)) (LamAnn (Inf (Vec (Inf (Bound 2)) (Inf (Bound 1)))) (Cons (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))
