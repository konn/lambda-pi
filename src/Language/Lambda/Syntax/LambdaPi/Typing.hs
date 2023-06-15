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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | FIXME: Stop using mere type instance, but use GADTs to make pattern-matching concise
module Language.Lambda.Syntax.LambdaPi.Typing (
  -- * Conversion from Renamed AST
  toInferable,
  toCheckable,

  -- * Type checking and inference
  Context (..),
  VarInfo (..),
  toEvalContext,
  Env (..),
  Value (..),
  Type,
  typeCheck,
  typeInfer,

  -- * ASTs
  Typing,
  Typed,
  Eval,
  XExprTyping (..),
  TypingMode (..),
  STypingMode (..),
  KnownTypingMode (..),
  Inferable,
  Checkable,
) where

import Control.Applicative ((<|>))
import Control.Lens hiding (Context)
import Control.Monad (unless)
import Data.Bifunctor qualified as Bi
import Data.DList.DNonEmpty qualified as DLNE
import Data.Either.Validation
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IntMap.Strict (IntMap)
import Data.List
import Data.Map qualified as Map
import Data.Semialign.Indexed
import Data.Semigroup.Generic
import Data.Text (Text)
import Data.Text qualified as T
import Data.These (These (..))
import Data.Tuple (swap)
import Debug.Trace qualified as DT
import GHC.Generics (Generic)
import GHC.Stack
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Eval
import Language.Lambda.Syntax.LambdaPi.Rename
import Text.PrettyPrint.Monadic (Pretty (..))

toInferable :: Expr Rename -> Maybe (Expr Inferable)
toInferable = \case
  Ann NoExtField l r -> Ann NoExtField <$> toCheckable l <*> toCheckable r
  Star NoExtField -> pure $ Star NoExtField
  App NoExtField l r -> App NoExtField <$> toInferable l <*> toCheckable r
  Var NoExtField (Global NoExtField v) -> pure $ Var Unbound $ Global NoExtField v
  Var NoExtField (PrimName NoExtField v) -> pure $ Var Unbound $ PrimName NoExtField v
  Var NoExtField (Bound NoExtField v) -> pure $ Var Unbound $ Bound NoExtField v
  Var NoExtField (XName c) -> noExtCon c
  Lam NoExtField v minType body -> do
    Lam NoExtField v <$> (toCheckable =<< minType) <*> toInferable body
  Pi NoExtField mv srcTy dstTy ->
    Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Let NoExtField v e b ->
    Let NoExtField v <$> toInferable e <*> toInferable b
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
  Open NoExtField b f -> Open NoExtField <$> toInferable b <*> toInferable f
  Variant _ (VariantTags fs) ->
    Variant NoExtField . VariantTags
      <$> mapM (mapM toCheckable) fs
  Inj {} -> Nothing
  Case NoExtField e (CaseAlts alts) ->
    Case NoExtField
      <$> toInferable e
      <*> ( CaseAlts
              <$> mapM
                ( mapM $ \(CaseAlt NoExtField mv bdy) ->
                    CaseAlt NoExtField mv <$> toInferable bdy
                )
                alts
          )
  XExpr x -> noExtCon x

inf :: Expr Inferable -> Expr Checkable
inf = XExpr . Inf

toCheckable :: Expr Rename -> Maybe (Expr Checkable)
toCheckable = \case
  Ann NoExtField l r -> fmap inf . Ann NoExtField <$> toCheckable l <*> toCheckable r
  Star NoExtField -> pure $ inf $ Star NoExtField
  App NoExtField l r -> fmap inf . App NoExtField <$> toInferable l <*> toCheckable r
  Var NoExtField (Global _ v) -> pure $ inf $ Var Unbound $ Global NoExtField v
  Var NoExtField (PrimName _ v) -> pure $ inf $ Var Unbound $ PrimName NoExtField v
  Var NoExtField (Bound _ v) -> pure $ inf $ Var Unbound $ Bound NoExtField v
  Var NoExtField (XName c) -> noExtCon c
  Lam NoExtField mv (Just ty) body ->
    do
      fmap inf . Lam NoExtField mv <$> toCheckable ty <*> toInferable body
      <|> Lam NoExtField mv . Just <$> toCheckable ty <*> toCheckable body
  Lam NoExtField mv Nothing body -> do
    Lam NoExtField mv Nothing <$> toCheckable body
  Pi NoExtField mv srcTy dstTy ->
    fmap inf . Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Let NoExtField v e b ->
    Let NoExtField v <$> toInferable e <*> toCheckable b
      <|> fmap inf . Let NoExtField v <$> toInferable e <*> toInferable b
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
  Open NoExtField r b ->
    Open NoExtField <$> toInferable r <*> toCheckable b
      <|> fmap inf . Open NoExtField <$> toInferable r <*> toInferable b
  Variant NoExtField (VariantTags fs) ->
    inf . Variant NoExtField . VariantTags
      <$> mapM (mapM toCheckable) fs
  Inj NoExtField tag a -> Inj NoExtField tag <$> toCheckable a
  Case NoExtField e (CaseAlts alts) ->
    Case NoExtField
      <$> toInferable e
      <*> ( CaseAlts
              <$> mapM
                ( mapM $ \(CaseAlt NoExtField mv bdy) ->
                    CaseAlt NoExtField mv <$> toCheckable bdy
                )
                alts
          )
      <|> fmap inf . Case NoExtField
        <$> toInferable e
        <*> ( CaseAlts
                <$> mapM
                  ( mapM $ \(CaseAlt NoExtField mv bdy) ->
                      CaseAlt NoExtField mv <$> toInferable bdy
                  )
                  alts
            )
  XExpr x -> noExtCon x

data VarInfo = VarInfo {varType :: Type, varValue :: Maybe Value}
  deriving (Show, Eq, Ord, Generic)

data Context = Context
  { globals :: HashMap Text VarInfo
  , locals :: IntMap Type
  }
  deriving (Show, Eq, Ord, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid Context

type Result = Either String

type Typed = Eval

toEvalContext :: Context -> Env
toEvalContext ctx =
  mempty
    & #namedBinds
      .~ HM.mapMaybe varValue (ctx ^. #globals)

{- & #localBinds
  .~ fmap
    (\(ty, k) -> vfree ty $ XName $ EvLocal k)
    (ctx ^. #bounds) -}

addLocal :: Int -> Type -> Context -> Context
addLocal i ty = #locals . at i ?~ ty

lookupName :: Name Inferable -> Context -> Maybe VarInfo
lookupName (XName (Local i)) ctx =
  ctx ^? #locals . ix i . to (`VarInfo` Nothing)
lookupName (Global _ t) ctx = ctx ^? #globals . ix t
lookupName _ _ = Nothing

typeCheck :: HasCallStack => Int -> Context -> Expr Checkable -> Type -> Result (Expr Eval)
typeCheck i ctx e ty | DT.trace ("Checking: " <> show (i, ctx, pprint e, ty)) False = error "No"
typeCheck i ctx (XExpr (Inf e)) ty = do
  (ty', e') <- typeInfer i ctx e

  unless (ty == ty') $
    Left $
      "Type mismatch: (expr, expected, actual) = "
        <> show (pprint e, pprint ty, pprint ty')
  pure e'
typeCheck i ctx (MkRecord NoExtField (MkRecordFields flds)) (VRecord fldTys) = do
  -- TODO: Consider structural subtyping
  fldTyped <-
    validationToEither $
      Bi.first (("Checking record expression failed: " <>) . unlines . DLNE.toList) $
        sequenceA $
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
            fldTys
  pure $ MkRecord fldTys $ MkRecordFields $ toOrderedList fldTyped
typeCheck _ _ mkRec@MkRecord {} ty =
  Left $
    "Expected a term of type `"
      <> show (pprint ty)
      <> "', but got a record: "
      <> show (pprint mkRec)
typeCheck _ _ (ProjField c _ _) _ = noExtCon c
typeCheck i ctx (Lam NoExtField v _ e) (VPi _ ty ty') = do
  e' <-
    typeCheck
      (i + 1)
      (addLocal i ty ctx)
      (substBVar 0 (XName (Local i)) e)
      (ty' $ vfree ty $ XName (EvLocal i))
  pure $ Lam LambdaTypeSpec {lamArgType = ty, lamBodyType = ty'} v (quote i ty) e'
typeCheck _ _ lam@(Lam NoExtField _ _ _) ty =
  Left $
    "Expected a term of type `"
      <> show (pprint ty)
      <> "', but got a lambda: "
      <> show (pprint lam)
typeCheck i ctx (Let NoExtField v e b) ty = do
  (vty, e') <- typeInfer i ctx e
  b' <-
    typeCheck
      (i + 1)
      (addLocal i vty ctx)
      (substBVar 0 (XName (Local i)) b)
      ty
  pure $ Let ty v e' b'
typeCheck i ctx (Open _ r b) ty = do
  (recType, e) <- typeInfer i ctx r
  -- FIXME: we need the explicit list of fields after structural subtyping is introduced; otherwise the system is unsound!
  case recType of
    VRecord fldTys -> do
      let newCtx = HM.map (`VarInfo` Nothing) fldTys
          ctx' = ctx & #globals %~ (newCtx <>)
      -- FIXME: We have to treat substitution correctly (back to BoundVar)
      b' <- typeCheck i ctx' b ty
      pure $ Open ty e b'
    otr ->
      Left $
        "open expression requires a record, but got a term of type: "
          <> show (pprint otr)
typeCheck i ctx inj@(Inj _ l e) vvar@(VVariant tags) =
  case HM.lookup l tags of
    Nothing ->
      Left $
        "The tag `"
          <> T.unpack l
          <> "' of expression `"
          <> show (pprint inj)
          <> "is not in the expected variant tags: "
          <> show vvar
    Just ty -> Inj tags l <$> typeCheck i ctx e ty
typeCheck _ _ inj@Inj {} ty =
  Left $
    "Expected type `"
      <> show (pprint ty)
      <> "', but got a variant: "
      <> show (pprint inj)
typeCheck i ctx (Case _ e (CaseAlts alts)) ty = do
  (eTy, e') <- typeInfer i ctx e
  case eTy ^? #_VVariant of
    Nothing ->
      Left $
        "A variant is expected in a case-expression, but a term of type: "
          <> show (pprint eTy)
    Just tagTys -> do
      rets <-
        Bi.first (("Checking case-expression failed: " <>) . unlines . DLNE.toList) $
          validationToEither $
            sequenceA $
              ialignWith
                ( \tag -> \case
                    This {} ->
                      -- TODO: should we allow this and just warn about redundancy?
                      Failure $ DLNE.singleton $ "Alternative for tag `" <> T.unpack tag <> "' is specified, but the given variant doesn't have that tag: " <> show (pprint eTy)
                    That {} ->
                      Failure $ DLNE.singleton $ "Variant has a tag `" <> T.unpack tag <> "', but no alternative is given"
                    These (CaseAlt _ n bdy) tty ->
                      Bi.first
                        ( DLNE.singleton
                            . ( ( "Type error during checking clause for `"
                                    <> T.unpack tag
                                    <> "': "
                                )
                                  <>
                              )
                        )
                        $ eitherToValidation
                        $ do
                          bdy' <-
                            typeCheck
                              (i + 1)
                              (addLocal i tty ctx)
                              (substBVar 0 (XName (Local i)) bdy)
                              ty
                          pure
                            ( tty
                            , CaseAlt
                                { xCaseAlt = NoExtField
                                , altName = n
                                , altBody = bdy'
                                }
                            )
                )
                (HM.fromList alts)
                tagTys
      pure
        $ Case
          CaseTypeInfo {caseRetTy = eTy, caseAltArgs = fst <$> rets}
          e'
        $ CaseAlts
        $ toOrderedList
        $ snd <$> rets
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
typeCheck _ _ (Variant c _) _ = noExtCon c

typeInfer :: HasCallStack => Int -> Context -> Expr Inferable -> Result (Type, Expr Eval)
typeInfer i ctx e | DT.trace ("Inferring: " <> show (i, ctx, pprint e)) False = error "No"
typeInfer !i ctx (Ann _ e rho) = do
  rho' <- typeCheck i ctx rho VStar
  let !t = eval (toEvalContext ctx) rho'
  e' <- typeCheck i ctx e t
  pure (t, Ann t e' rho')
typeInfer _ _ Star {} = pure (VStar, Star NoExtField)
typeInfer _ _ (Var site (PrimName _ p)) =
  let pTy = inferPrim p
   in pure (pTy, Var pTy $ fromBoundSite (PrimName NoExtField p) site)
typeInfer _ ctx (Var src x) = case lookupName x ctx of
  Just VarInfo {varType = t} ->
    pure
      ( t
      , case src of
          OrigBVar i -> Var t $ Bound NoExtField i
          Unbound -> Var t $ toEvalName x
      )
  Nothing -> Left $ "Unknown identifier: " <> show x
typeInfer !i ctx ex@(App NoExtField f x) = do
  let ctx' = toEvalContext ctx
  typeInfer i ctx f >>= \case
    (VPi _ t t', f') -> do
      x' <- typeCheck i ctx x t
      let retTy = t' $ eval ctx' x'
      pure (retTy, App retTy f' x')
    (ty, _) ->
      Left $
        "LHS of application must be a function, but got: "
          <> show (pprint f, pprint ty)
          <> "; during evaluating "
          <> show (pprint ex)
typeInfer i ctx l@(Lam NoExtField mv ty body) = do
  let ctx' = toEvalContext ctx
  ty' <- typeCheck i ctx ty VStar
  () <- DT.trace ("infer/Lam: Evaluating: " <> show (ctx, ctx', ty, ty', pprint ty') <> " (as part of " <> show (l) <> ")") $ pure ()
  let tyVal = eval ctx' ty'
  (bodyTy, body') <-
    typeInfer
      (i + 1)
      (addLocal i tyVal ctx)
      $ substBVar 0 (XName $ Local i) body
  let lamRetTy v = substBound i v bodyTy
      lamTy = VPi mv tyVal lamRetTy
  pure (lamTy, Lam LambdaTypeSpec {lamBodyType = lamRetTy, lamArgType = tyVal} mv ty' body')
typeInfer i ctx l@(Pi NoExtField mv arg ret) = do
  arg' <- typeCheck i ctx arg VStar
  let ctx' = toEvalContext ctx
  () <- DT.trace ("infer/Pi: Evaluating: " <> show (ctx, ctx', arg', pprint arg') <> " (as part of " <> show (pprint l) <> ")") $ pure ()
  let t = eval ctx' arg'

  ret' <-
    typeCheck
      (i + 1)
      (addLocal i t ctx)
      (substBVar 0 (XName $ Local i) ret)
      VStar
  pure (VStar, Pi NoExtField mv arg' ret')
typeInfer i ctx (Let NoExtField mv e b) = do
  (vty, e') <- typeInfer i ctx e
  (ty, b') <-
    typeInfer
      (i + 1)
      (addLocal i vty ctx)
      $ substBVar 0 (XName $ Local i) b
  pure (ty, Let ty mv e' b')
typeInfer _ _ Nat {} = pure (VStar, Nat NoExtField)
typeInfer _ _ Zero {} = pure (VNat, Zero VNat)
typeInfer i ctx (Succ NoExtField k) = (VNat,) . Succ NoExtField <$> typeCheck i ctx k VNat
typeInfer i ctx (NatElim NoExtField m mz ms k) = do
  m' <- typeCheck i ctx m $ VPi (AlphaName "k") VNat $ const VStar
  let mVal = eval (toEvalContext ctx) m'
  mz' <- typeCheck i ctx mz $ mVal @@ VZero
  ms' <- typeCheck i ctx ms $
    VPi (AlphaName "l") VNat $ \l ->
      VPi Anonymous (mVal @@ l) $ const $ mVal @@ VSucc l
  k' <- typeCheck i ctx k VNat
  let kVal = eval (toEvalContext ctx) k'
      retTy = mVal @@ kVal
  pure (retTy, NatElim retTy m' mz' ms' k')
typeInfer i ctx (Vec NoExtField a k) =
  fmap (VStar,) . Vec NoExtField <$> typeCheck i ctx a VStar <*> typeCheck i ctx k VNat
typeInfer i ctx (Nil NoExtField a) = do
  a' <- typeCheck i ctx a VStar
  let retTy = VVec (eval (toEvalContext ctx) a') VZero
  pure (retTy, Nil NoExtField a')
typeInfer i ctx (Cons NoExtField a n x xs) = do
  a' <- typeCheck i ctx a VStar
  n' <- typeCheck i ctx n VNat
  let ctx' = toEvalContext ctx
      aVal = eval ctx' a'
      nVal = eval ctx' n'
  x' <- typeCheck i ctx x aVal
  xs' <- typeCheck i ctx xs $ VVec aVal nVal
  pure (VVec aVal $ VSucc nVal, Cons NoExtField a' n' x' xs')
typeInfer i ctx (VecElim NoExtField a m mnil mcons n vs) = do
  let ctx' = toEvalContext ctx
  a' <- typeCheck i ctx a VStar
  let !aVal = eval ctx' a'
  m' <- typeCheck i ctx m $
    VPi (AlphaName "k") VNat $ \k ->
      VPi Anonymous (VVec aVal k) $ const VStar
  let !mVal = eval ctx' m'
  !mnil' <-
    typeCheck i ctx mnil $
      vapps [mVal, VZero, VNil aVal]
  !mcons' <- typeCheck i ctx mcons $
    VPi (AlphaName "k") VNat $ \k ->
      VPi (AlphaName "y") aVal $ \y ->
        VPi (AlphaName "ys") (VVec aVal k) $ \ys ->
          VPi Anonymous (vapps [mVal, k, ys]) $
            const $
              vapps [mVal, VSucc k, VCons aVal k y ys]
  !n' <- typeCheck i ctx n VNat
  let !nVal = eval ctx' n'
  vs' <- typeCheck i ctx vs $ VVec aVal nVal
  let !vsVal = eval ctx' vs'
      !retTy = vapps [mVal, nVal, vsVal]
  pure (retTy, VecElim retTy a' m' mnil' mcons' n' vs')
typeInfer i ctx (Record NoExtField flds) =
  (VStar,) . Record NoExtField . RecordFieldTypes
    <$> traverse (traverse $ flip (typeCheck i ctx) VStar) (recFieldTypes flds)
typeInfer i ctx (MkRecord NoExtField (MkRecordFields flds)) = do
  fldTysFlds <- HM.fromList <$> traverse (traverse (typeInfer i ctx)) flds
  let fldTys = HM.map fst fldTysFlds
      flds' = MkRecordFields $ toOrderedList $ HM.map snd fldTysFlds
  pure (VRecord fldTys, MkRecord fldTys flds')
typeInfer !i ctx (ProjField NoExtField e f) =
  typeInfer i ctx e >>= \case
    (VRecord flds, e') ->
      case HM.lookup f flds of
        Just ty -> pure (ty, ProjField ty e' f)
        Nothing ->
          Left $
            "Record doesn't have the required field `"
              <> T.unpack f
              <> "': "
              <> show (map fst $ toOrderedList flds)
    (ty, _) ->
      Left $
        "LHS of record projection must be record, but got: "
          <> show (e, pprint ty)
typeInfer i ctx (Open _ r b) = do
  (recType, r') <- typeInfer i ctx r
  -- FIXME: we need the explicit list of fields after structural subtyping is introduced; otherwise the system is unsound!
  case recType of
    VRecord fldTys -> do
      let newCtx = HM.map (`VarInfo` Nothing) fldTys
          ctx' = ctx & #globals %~ (newCtx <>)
      -- FIXME: We have to treat substitution correctly (back to BoundVar)
      (retTy, b') <- typeInfer i ctx' b
      pure (retTy, Open retTy r' b')
    otr ->
      Left $
        "open expression requires a record, but got a term of type: "
          <> show (pprint otr)
typeInfer i ctx (Variant NoExtField (VariantTags fs)) =
  (VStar,) . Variant NoExtField . VariantTags
    <$> traverse (traverse $ flip (typeCheck i ctx) VStar) fs
typeInfer i ctx (Case NoExtField e (CaseAlts alts)) = do
  (eTy, e') <- typeInfer i ctx e
  case eTy ^? #_VVariant of
    Nothing ->
      Left $
        "A variant is expected in a case-expression, but a term of type: "
          <> show (pprint eTy)
    Just tagTys -> do
      altTys <-
        Bi.first (("Checking case-expression failed: " <>) . unlines . DLNE.toList) $
          validationToEither $
            sequenceA $
              ialignWith
                ( \tag -> \case
                    This {} ->
                      -- TODO: should we allow this and just warn about redundancy?
                      Failure $ DLNE.singleton $ "Alternative for tag `" <> T.unpack tag <> "' is specified, but the given variant doesn't have that tag: " <> show (pprint eTy)
                    That {} ->
                      Failure $ DLNE.singleton $ "Variant has a tag `" <> T.unpack tag <> "', but no alternative is given"
                    These (CaseAlt _ mv bdy) tty ->
                      Bi.first
                        ( DLNE.singleton
                            . ( ( "Type error during checking clause for `"
                                    <> T.unpack tag
                                    <> "': "
                                )
                                  <>
                              )
                        )
                        $ eitherToValidation
                        $ fmap (CaseAlt NoExtField mv)
                          <$> typeInfer
                            (i + 1)
                            (addLocal i tty ctx)
                            (substBVar 0 (XName $ Local i) bdy)
                )
                (HM.fromList alts)
                tagTys
      let tyMaps =
            Map.fromListWith (<>) $
              map (Bi.second DLNE.singleton . swap) $
                HM.toList $
                  fst <$> altTys
      case Map.keys tyMaps of
        [] -> Left "Empty alternative!"
        [ty] ->
          pure
            ( ty
            , Case
                CaseTypeInfo
                  { caseAltArgs = fst <$> altTys
                  , caseRetTy = ty
                  }
                e'
                $ CaseAlts [(l, alt) | (l, (_, alt)) <- toOrderedList altTys]
            )
        _ ->
          Left $
            "Type mismatch: distinct returned types: "
              <> show (map pprint $ Map.keys tyMaps)
typeInfer _ _ (Inj c _ _) = noExtCon c
typeInfer _ _ (XExpr c) = case c of {}

fromBoundSite :: Name Eval -> BoundSource -> Name Eval
fromBoundSite v Unbound = v
fromBoundSite _ (OrigBVar i) = Bound NoExtField i

toEvalName :: Name (Typing m) -> Name Eval
toEvalName (Global _ v) = Global NoExtField v
toEvalName (Bound _ v) = Bound NoExtField v
toEvalName (PrimName _ v) = PrimName NoExtField v
toEvalName (XName (Local v)) = XName (EvLocal v)

inferPrim :: Prim -> Type
inferPrim Tt = VNeutral $ NPrim VStar Unit
inferPrim Unit = VStar

substBVar :: forall m. KnownTypingMode m => Int -> Name Inferable -> Expr (Typing m) -> Expr (Typing m)
substBVar !i r (Ann c e ty) = Ann c (substBVar i r e) (substBVar i r ty)
substBVar !_ _ (Star c) = Star c
substBVar !i r bd@(Var _ (Bound _ j))
  | i == j = fromInferable $ Var (OrigBVar j) r
  | otherwise = bd
substBVar !_ _ f@Var {} = f
substBVar !i r (App e f g) = App e (substBVar i r f) (substBVar i r g)
substBVar !i r (Lam x mv ann body) =
  case typingModeVal @m of
    SCheck -> Lam x mv (substBVar i r <$> ann) $ substBVar (i + 1) r body
    SInfer -> Lam x mv (substBVar i r ann) $ substBVar (i + 1) r body
substBVar !i r (Pi c mv ann body) =
  Pi c mv (substBVar i r ann) (substBVar (i + 1) r body)
substBVar !i r (Let NoExtField mv e b) =
  Let NoExtField mv (substBVar i r e) $ substBVar (i + 1) r b
substBVar _ _ (Nat c) = Nat c
substBVar _ _ (Zero c) = Zero c
substBVar i r (Succ c n) = Succ c $ substBVar i r n
substBVar i r (NatElim c t b ih n) =
  NatElim c (substBVar i r t) (substBVar i r b) (substBVar i r ih) (substBVar i r n)
substBVar i r (Vec c a n) = Vec c (substBVar i r a) (substBVar i r n)
substBVar i r (Nil c a) = Nil c $ substBVar i r a
substBVar i r (Cons c a n x xs) =
  Cons c (substBVar i r a) (substBVar i r n) (substBVar i r x) (substBVar i r xs)
substBVar i r (VecElim c a t b ih n xs) =
  VecElim c (substBVar i r a) (substBVar i r t) (substBVar i r b) (substBVar i r ih) (substBVar i r n) (substBVar i r xs)
substBVar i r (Record c (RecordFieldTypes flds)) =
  Record c $ RecordFieldTypes $ map (fmap (substBVar i r)) flds
substBVar i r (MkRecord c (MkRecordFields flds)) =
  case typingModeVal @m of
    SCheck -> MkRecord c $ MkRecordFields $ map (fmap (substBVar i r)) flds
    SInfer -> MkRecord c $ MkRecordFields $ map (fmap (substBVar i r)) flds
substBVar i r (ProjField c e f) =
  ProjField c (substBVar i r e) f
substBVar i r (Open NoExtField rc b) =
  Open NoExtField (substBVar i r rc) (substBVar i r b)
substBVar !i r (XExpr (Inf e)) = XExpr $ Inf $ substBVar i r e
substBVar i r (Variant c (VariantTags flds)) =
  Variant c $ VariantTags $ map (fmap (substBVar i r)) flds
substBVar i r (Case c e (CaseAlts alts)) =
  Case
    c
    (substBVar i r e)
    $ CaseAlts
    $ map
      ( fmap $ \(CaseAlt d mv b) ->
          CaseAlt d mv $ substBVar (i + 1) r b
      )
      alts
substBVar i r (Inj c l e) = Inj c l $ substBVar i r e

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

toOrderedList :: HashMap Text a -> [(Text, a)]
toOrderedList = sortOn fst . HM.toList

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

type Inferable = Typing 'Infer

type Checkable = Typing 'Check

type instance XAnn Inferable = NoExtField

type instance XAnn Checkable = NoExtCon

type instance AnnLHS (Typing m) = Expr Checkable

type instance AnnRHS (Typing m) = Expr Checkable

type instance XStar Inferable = NoExtField

type instance XStar Checkable = NoExtCon

type instance XVar Inferable = BoundSource

data BoundSource = Unbound | OrigBVar !Int
  deriving (Show, Eq, Ord, Generic)

type instance XVar Checkable = NoExtCon

newtype TypingVar = Local Int
  deriving (Show, Eq, Ord, Generic)

instance VarLike TypingVar where
  varName (Local i) = do
    mtn <- preview $ #boundVars . ix i
    case mtn of
      Just (t, n) -> pure $ Just $ t <> if n > 0 then "_" <> T.pack (show n) else mempty
      Nothing ->
        pure $
          Just $
            "<<Local: " <> T.pack (show i) <> ">>"

type instance XName (Typing _) = TypingVar

type instance XGlobal (Typing _) = NoExtField

type instance XBound (Typing _) = NoExtField

type instance XPrimName (Typing _) = NoExtField

type instance Id (Typing m) = Name (Typing m)

type instance XApp Inferable = NoExtField

type instance XApp Checkable = NoExtCon

type instance AppLHS (Typing _) = Expr Inferable

type instance AppRHS (Typing _) = Expr Checkable

type instance XLam (Typing _) = NoExtField

type instance LamBindName (Typing m) = AlphaName

type instance LamBindType Inferable = Expr Checkable

type instance LamBindType Checkable = Maybe (Expr Checkable)

type instance LamBody (Typing m) = Expr (Typing m)

type instance XPi Inferable = NoExtField

type instance XPi Checkable = NoExtCon

type instance PiVarName (Typing _) = AlphaName

type instance PiVarType (Typing _) = Expr Checkable

type instance PiRHS (Typing _) = Expr Checkable

type instance XLet (Typing _) = NoExtField

type instance LetName (Typing _) = AlphaName

type instance LetRHS (Typing _) = Expr Inferable

type instance LetBody (Typing e) = Expr (Typing e)

type instance XNat Inferable = NoExtField

type instance XNat Checkable = NoExtCon

type instance XZero Inferable = NoExtField

type instance XZero Checkable = NoExtCon

type instance XSucc Inferable = NoExtField

type instance XSucc Checkable = NoExtCon

type instance SuccBody (Typing _) = Expr Checkable

type instance XNatElim Inferable = NoExtField

type instance XNatElim Checkable = NoExtCon

type instance NatElimRetFamily (Typing _) = Expr Checkable

type instance NatElimBaseCase (Typing _) = Expr Checkable

type instance NatElimInductionStep (Typing _) = Expr Checkable

type instance NatElimInput (Typing _) = Expr Checkable

type instance XVec Inferable = NoExtField

type instance XVec Checkable = NoExtCon

type instance VecType (Typing _) = Expr Checkable

type instance VecLength (Typing _) = Expr Checkable

type instance XNil Inferable = NoExtField

type instance XNil Checkable = NoExtCon

type instance NilType (Typing _) = Expr Checkable

type instance XCons Inferable = NoExtField

type instance XCons Checkable = NoExtCon

type instance ConsType (Typing _) = Expr Checkable

type instance ConsLength (Typing _) = Expr Checkable

type instance ConsHead (Typing _) = Expr Checkable

type instance ConsTail (Typing _) = Expr Checkable

type instance XVecElim Inferable = NoExtField

type instance XVecElim Checkable = NoExtCon

type instance VecElimEltType (Typing _) = Expr Checkable

type instance VecElimRetFamily (Typing _) = Expr Checkable

type instance VecElimBaseCase (Typing _) = Expr Checkable

type instance VecElimInductiveStep (Typing _) = Expr Checkable

type instance VecElimLength (Typing _) = Expr Checkable

type instance VecElimInput (Typing _) = Expr Checkable

type instance XRecord Inferable = NoExtField

type instance XRecord Checkable = NoExtCon

type instance RecordFieldType (Typing _) = Expr Checkable

type instance XProjField Inferable = NoExtField

type instance XProjField Checkable = NoExtCon

type instance ProjFieldRecord (Typing _) = Expr Inferable

type instance XMkRecord (Typing _) = NoExtField

type instance RecordField (Typing m) = Expr (Typing m)

type instance XOpen (Typing m) = NoExtField

type instance OpenRecord (Typing m) = Expr Inferable

type instance OpenBody (Typing m) = Expr (Typing m)

type instance XVariant (Typing 'Infer) = NoExtField

type instance XVariant (Typing 'Check) = NoExtCon

type instance VariantArgType (Typing p) = Expr Checkable

type instance XInj Inferable = NoExtCon

type instance XInj Checkable = NoExtField

type instance InjArg (Typing e) = Expr (Typing e)

type instance XCase (Typing _) = NoExtField

type instance CaseArg (Typing _) = Expr Inferable

type instance XCaseAlt (Typing m) = NoExtField

type instance CaseAltVarName (Typing _) = AlphaName

type instance CaseAltBody (Typing m) = Expr (Typing m)

type instance XExpr (Typing m) = XExprTyping m

data XExprTyping m where
  Inf :: Expr Inferable -> XExprTyping 'Check

deriving instance Show (XExprTyping m)

deriving instance Eq (XExprTyping m)

deriving instance Ord (XExprTyping m)

instance Pretty PrettyEnv (XExprTyping m) where
  pretty (Inf e) = pretty e
