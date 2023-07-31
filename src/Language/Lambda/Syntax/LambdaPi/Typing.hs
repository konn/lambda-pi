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
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant bracket" #-}

-- | FIXME: Stop using mere type instance, but use GADTs to make pattern-matching concise
module Language.Lambda.Syntax.LambdaPi.Typing (
  -- * Conversion from Renamed AST
  toInferable,
  toCheckable,

  -- * Type checking and inference
  Context' (..),
  Context,
  VarInfo' (..),
  VarInfo,
  toEvalContext,
  Env' (..),
  Value' (..),
  Value,
  Type,
  Neutral' (..),
  Neutral,
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
import Control.Lens hiding (Context, Context')
import Control.Monad (unless)
import Data.Bifunctor qualified as Bi
import Data.DList.DNonEmpty qualified as DLNE
import Data.Data (Data)
import Data.Either.Validation
import Data.Generics.Labels ()
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.Level
import Data.List
import Data.Map qualified as Map
import Data.Semialign.Indexed
import Data.Semigroup.Generic
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Text qualified as T
import Data.These (These (..))
import Data.Tuple (swap)
import GHC.Generics (Generic)
import GHC.Stack
import Language.Lambda.Syntax.LambdaPi
import Language.Lambda.Syntax.LambdaPi.Eval
import Language.Lambda.Syntax.LambdaPi.Rename (Rename)
import Text.PrettyPrint.Monadic (Pretty (..))

toInferable :: Expr Rename -> Maybe (Expr Inferable)
toInferable = \case
  Ann NoExtField l r -> Ann NoExtField <$> toCheckable l <*> toCheckable r
  Star NoExtField -> pure $ Star NoExtField
  App NoExtField l r -> App NoExtField <$> toInferable l <*> toCheckable r
  Var NoExtField (Global NoExtField v) -> pure $ Var NoExtField $ Global NoExtField v
  Var NoExtField (PrimName NoExtField v) -> pure $ Var NoExtField $ PrimName NoExtField v
  Var NoExtField (Bound NoExtField v) -> pure $ Var NoExtField $ Bound NoExtField v
  Var NoExtField (XName c) -> noExtCon c
  Lam NoExtField v minType body -> do
    Lam NoExtField v <$> (toCheckable =<< minType) <*> toInferable body
  Pi NoExtField mv srcTy dstTy ->
    Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Sigma NoExtField mv srcTy dstTy ->
    Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Pair {} -> Nothing
  Split {} -> Nothing
  Let NoExtField v e b ->
    Let NoExtField v <$> toInferable e <*> toInferable b
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

inf :: Expr (Inferable' n) -> Expr (Checkable' n)
inf = XExpr . Inf

toCheckable :: Expr Rename -> Maybe (Expr Checkable)
toCheckable = \case
  Ann NoExtField l r -> fmap inf . Ann NoExtField <$> toCheckable l <*> toCheckable r
  Star NoExtField -> pure $ inf $ Star NoExtField
  App NoExtField l r -> fmap inf . App NoExtField <$> toInferable l <*> toCheckable r
  Var NoExtField (Global _ v) -> pure $ inf $ Var NoExtField $ Global NoExtField v
  Var NoExtField (PrimName _ v) -> pure $ inf $ Var NoExtField $ PrimName NoExtField v
  Var NoExtField (Bound _ v) -> pure $ inf $ Var NoExtField $ Bound NoExtField v
  Var NoExtField (XName c) -> noExtCon c
  Lam NoExtField mv (Just ty) body ->
    do
      fmap inf . Lam NoExtField mv <$> toCheckable ty <*> toInferable body
      <|> Lam NoExtField mv . Just <$> toCheckable ty <*> toCheckable body
  Lam NoExtField mv Nothing body -> do
    Lam NoExtField mv Nothing <$> toCheckable body
  Pi NoExtField mv srcTy dstTy ->
    fmap inf . Pi NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Sigma NoExtField mv srcTy dstTy ->
    fmap inf . Sigma NoExtField mv <$> toCheckable srcTy <*> toCheckable dstTy
  Pair NoExtField l r ->
    Pair NoExtField <$> toCheckable l <*> toCheckable r
  Split NoExtField scrut2 l r b ->
    Split NoExtField <$> toInferable scrut2 <*> pure l <*> pure r <*> toCheckable b
  Let NoExtField v e b ->
    Let NoExtField v <$> toInferable e <*> toCheckable b
      <|> fmap inf . Let NoExtField v <$> toInferable e <*> toInferable b
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

type VarInfo = VarInfo' Z

data VarInfo' n = VarInfo {varType :: Type' n, varValue :: Maybe (Value' n)}
  deriving (Show, Eq, Ord, Generic)

type Context = Context' Z

data Context' n = Context
  { globals :: HashMap Text (VarInfo' n)
  , locals :: Seq (Type' n)
  }
  deriving (Show, Eq, Ord, Generic)
  deriving (Semigroup, Monoid) via GenericSemigroupMonoid (Context' n)

type Result = Either String

type Typed = Eval

toEvalContext :: forall n. Context' n -> Env' n
toEvalContext ctx =
  mempty @(Env' n)
    & #namedBinds .~ HM.mapMaybe varValue ctx.globals

addLocal :: Type' n -> Context' n -> Context' ('S n)
addLocal ty ctx =
  let te = ThawEnv {curLvl = 0}
   in ctx
        { locals =
            fmap
              (injValueWith te)
              $ ty <| ctx.locals
        , globals = injVarInfo te <$> ctx.globals
        }

injVarInfo :: ThawEnv n -> VarInfo' n -> VarInfo' (S n)
injVarInfo te vi =
  vi
    { varType = injValueWith te vi.varType
    , varValue = injValueWith te <$> vi.varValue
    }

lookupName :: Name (Inferable' n) -> Context' n -> Maybe (VarInfo' n)
lookupName (XName (Local i)) ctx =
  ctx ^? #locals . ix (fromOrd i) . to (`VarInfo` Nothing)
lookupName (Global _ t) ctx = ctx ^? #globals . ix t
lookupName _ _ = Nothing

injValueN :: Value' n -> Value' (S n)
injValueN = injValueWith ThawEnv {curLvl = 0}

typeCheck :: (HasCallStack) => Context' n -> Expr (Checkable' n) -> Type' n -> Result (Expr (Eval' n))
typeCheck ctx (XExpr (Inf e)) ty = do
  (ty', e') <- typeInfer ctx e

  unless (ty == ty') $
    Left $
      "Type mismatch: (expr, expected, actual) = "
        <> show (pprint e, pprint ty, pprint ty')
  pure e'
typeCheck ctx (Pair NoExtField l r) (VSigma _ ty ty') = do
  l' <- typeCheck ctx l ty
  let lVal = eval (toEvalContext ctx) l'
  r' <-
    thawLocal
      <$> typeCheck
        (addLocal ty ctx)
        (freezeBound 0 r)
        (injValueN $ ty' lVal)
  pure $
    Pair
      BinderTypeSpec
        { argType = ty
        , bodyType = ty'
        }
      l'
      r'
typeCheck _ Pair {} ty =
  Left $
    "Expected a term of type `"
      <> show (pprint ty)
      <> "', but got a pair (sigma-type)."
typeCheck ctx (Split _ scrut2 lName rName body) splitRetType = do
  (scrut2Ty, scrut2') <- typeInfer ctx scrut2
  case scrut2Ty of
    VSigma _ splitFstType splitSndType -> do
      body' <-
        thawLocal . thawLocal
          <$> typeCheck
            ( addLocal
                ( injBinder splitSndType $
                    vfree (injValueN splitFstType) $
                      XName $
                        EvLocal Here
                )
                $ addLocal splitFstType ctx
            )
            (freezeBound 1 $ freezeBound 0 body)
            ( injValueN $ injValueN splitRetType
            )
      pure $ Split SplitTypeInfo {..} scrut2' lName rName body'
    _ -> Left $ "A scrutinee of split-expression must be of Sigma-type, but has type : " <> show (pprint scrut2Ty)
typeCheck ctx (MkRecord NoExtField (MkRecordFields flds)) (VRecord fldTys) = do
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
                    $ typeCheck ctx f v
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
typeCheck _ mkRec@MkRecord {} ty =
  Left $
    "Expected a term of type `"
      <> show (pprint ty)
      <> "', but got a record: "
      <> show (pprint mkRec)
typeCheck _ (ProjField c _ _) _ = noExtCon c
typeCheck ctx (Lam NoExtField v _ e) (VPi _ ty ty') = do
  e' <-
    thawLocal
      <$> typeCheck
        (addLocal ty ctx)
        (freezeBound 0 e)
        (injBinder ty' $ vfree (injValueN ty) $ XName $ EvLocal Here)
  pure $
    Lam
      BinderTypeSpec
        { argType = ty
        , bodyType = ty'
        }
      v
      (quote 0 ty)
      e'
typeCheck _ lam@(Lam NoExtField _ _ _) ty =
  Left $
    "Expected a term of type `"
      <> show (pprint ty)
      <> "', but got a lambda: "
      <> show (pprint lam)
typeCheck ctx (Let NoExtField v e b) ty = do
  (vty, e') <- typeInfer ctx e
  b' <-
    thawLocal
      <$> typeCheck
        (addLocal vty ctx)
        (freezeBound 0 b)
        (injValueN ty)
  pure $ Let ty v e' b'
typeCheck ctx (Open _ r b) ty = do
  (recType, e) <- typeInfer ctx r
  -- FIXME: we need the explicit list of fields after structural subtyping is introduced; otherwise the system is unsound!
  case recType of
    VRecord fldTys -> do
      let newCtx = HM.map (`VarInfo` Nothing) fldTys
          ctx' = ctx & #globals %~ (newCtx <>)
      -- FIXME: We have to treat substitution correctly (back to BoundVar)
      b' <- typeCheck ctx' b ty
      pure $ Open ty e b'
    otr ->
      Left $
        "open expression requires a record, but got a term of type: "
          <> show (pprint otr)
typeCheck ctx inj@(Inj _ l e) vvar@(VVariant tags) =
  case HM.lookup l tags of
    Nothing ->
      Left $
        "The tag `"
          <> T.unpack l
          <> "' of expression `"
          <> show (pprint inj)
          <> "is not in the expected variant tags: "
          <> show vvar
    Just ty -> Inj tags l <$> typeCheck ctx e ty
typeCheck _ inj@Inj {} ty =
  Left $
    "Expected type `"
      <> show (pprint ty)
      <> "', but got a variant: "
      <> show (pprint inj)
typeCheck ctx (Case _ e (CaseAlts alts)) ty = do
  (eTy, e') <- typeInfer ctx e
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
                            thawLocal
                              <$> typeCheck
                                (addLocal tty ctx)
                                (freezeBound 0 bdy)
                                (injValueN ty)
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
typeCheck _ (Ann c _ _) _ = noExtCon c
typeCheck _ (Star c) _ = noExtCon c
typeCheck _ (Var c _) _ = noExtCon c
typeCheck _ (Pi c _ _ _) _ = noExtCon c
typeCheck _ (Sigma c _ _ _) _ = noExtCon c
typeCheck _ (App c _ _) _ = noExtCon c
typeCheck _ (Record c _) _ = noExtCon c
typeCheck _ (Variant c _) _ = noExtCon c

typeInfer :: (HasCallStack) => Context' n -> Expr (Inferable' n) -> Result (Type' n, Expr (Eval' n))
typeInfer ctx (Ann _ e rho) = do
  rho' <- typeCheck ctx rho VStar
  let !t = eval (toEvalContext ctx) rho'
  e' <- typeCheck ctx e t
  pure (t, Ann t e' rho')
typeInfer _ Star {} = pure (VStar, Star NoExtField)
typeInfer _ (Var _ (PrimName _ p)) =
  let pTy = inferPrim p
   in pure (pTy, Var pTy $ PrimName NoExtField p)
typeInfer ctx (Var _ x) = case lookupName x ctx of
  Just VarInfo {varType = t} ->
    pure (t, Var t $ toEvalName x)
  Nothing -> Left $ "Unknown identifier: " <> show x
typeInfer ctx ex@(App NoExtField f x) = do
  let ctx' = toEvalContext ctx
  typeInfer ctx f >>= \case
    (VPi _ t t', f') -> do
      x' <- typeCheck ctx x t
      let retTy = t' $ eval ctx' x'
      pure (retTy, App retTy f' x')
    (ty, _) ->
      Left $
        "LHS of application must be a function, but got: "
          <> show (pprint f, pprint ty)
          <> "; during evaluating "
          <> show (pprint ex)
typeInfer ctx (Lam NoExtField mv ty body) = do
  !ty' <- typeCheck ctx ty VStar
  let ctx' = toEvalContext ctx
      !tyVal = eval ctx' ty'
  (!bodyTy, !body') <-
    Bi.bimap thawLocalVal thawLocal
      <$> typeInfer (addLocal tyVal ctx) (freezeBound 0 body)
  let lamRetTy v = substBound 0 v bodyTy
      !lamTy = VPi mv tyVal lamRetTy
  pure
    ( lamTy
    , Lam
        BinderTypeSpec
          { bodyType = lamRetTy
          , argType = tyVal
          }
        mv
        ty'
        body'
    )
typeInfer ctx (Pi NoExtField mv arg ret) = do
  !arg' <- typeCheck ctx arg VStar
  let ctx' = toEvalContext ctx
      !t = eval ctx' arg'
  !ret' <-
    thawLocal
      <$> typeCheck (addLocal t ctx) (freezeBound 0 ret) VStar
  pure (VStar, Pi NoExtField mv arg' ret')
typeInfer ctx (Sigma NoExtField mv arg ret) = do
  !arg' <- typeCheck ctx arg VStar
  let ctx' = toEvalContext ctx
      !t = eval ctx' arg'
  !ret' <-
    thawLocal
      <$> typeCheck (addLocal t ctx) (freezeBound 0 ret) VStar
  pure (VStar, Sigma NoExtField mv arg' ret')
typeInfer _ (Pair c _ _) = noExtCon c
typeInfer _ (Split c _ _ _ _) = noExtCon c
typeInfer ctx (Let NoExtField mv e b) = do
  (!vty, !e') <- typeInfer ctx e
  (!ty, !b') <-
    Bi.bimap thawLocalVal thawLocal
      <$> typeInfer (addLocal vty ctx) (freezeBound 0 b)
  pure (ty, Let ty mv e' b')
typeInfer ctx (Record NoExtField flds) =
  (VStar,) . Record NoExtField . RecordFieldTypes
    <$> traverse (traverse $ flip (typeCheck ctx) VStar) (recFieldTypes flds)
typeInfer ctx (MkRecord NoExtField (MkRecordFields flds)) = do
  fldTysFlds <- HM.fromList <$> traverse (traverse (typeInfer ctx)) flds
  let fldTys = HM.map fst fldTysFlds
      flds' = MkRecordFields $ toOrderedList $ HM.map snd fldTysFlds
  pure (VRecord fldTys, MkRecord fldTys flds')
typeInfer ctx (ProjField NoExtField e f) =
  typeInfer ctx e >>= \case
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
typeInfer ctx (Open _ r b) = do
  (recType, r') <- typeInfer ctx r
  -- FIXME: we need the explicit list of fields after structural subtyping is introduced; otherwise the system is unsound!
  case recType of
    VRecord fldTys -> do
      let newCtx = HM.map (`VarInfo` Nothing) fldTys
          ctx' = ctx & #globals %~ (newCtx <>)
      -- FIXME: We have to treat substitution correctly (back to BoundVar)
      (retTy, b') <- typeInfer ctx' b
      pure (retTy, Open retTy r' b')
    otr ->
      Left $
        "open expression requires a record, but got a term of type: "
          <> show (pprint otr)
typeInfer ctx (Variant NoExtField (VariantTags fs)) =
  (VStar,) . Variant NoExtField . VariantTags
    <$> traverse (traverse $ flip (typeCheck ctx) VStar) fs
typeInfer ctx (Case NoExtField e (CaseAlts alts)) = do
  (eTy, e') <- typeInfer ctx e
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
                        $ bimap thawLocalVal (CaseAlt NoExtField mv . thawLocal)
                          <$> typeInfer (addLocal tty ctx) (freezeBound 0 bdy)
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
typeInfer _ (Inj c _ _) = noExtCon c
typeInfer _ (XExpr c) = case c of {}

toEvalName :: Name (Typing m n) -> Name (Eval' n)
toEvalName (Global _ v) = Global NoExtField v
toEvalName (Bound _ v) = Bound NoExtField v
toEvalName (PrimName _ v) = PrimName NoExtField v
toEvalName (XName (Local v)) = XName (EvLocal v)

freezeBound ::
  forall m n.
  (KnownTypingMode m) =>
  Int ->
  Expr (Typing m n) ->
  Expr (Typing m ('S n))
freezeBound !i (Ann c e ty) =
  Ann
    (case typingModeVal @m of SInfer -> c; SCheck -> c)
    (freezeBound i e)
    (freezeBound i ty)
freezeBound _ (Star c) =
  Star $ case typingModeVal @m of SInfer -> c; SCheck -> c
freezeBound i (Var ext n) =
  Var (case typingModeVal @m of SInfer -> ext; SCheck -> ext) $
    freezeBoundName i n
freezeBound i (App e f g) =
  App
    (case typingModeVal @m of SInfer -> e; SCheck -> e)
    (freezeBound i f)
    (freezeBound i g)
freezeBound i (Lam x mv ann body) =
  case typingModeVal @m of
    SCheck -> Lam x mv (freezeBound i <$> ann) $ freezeBound (i + 1) body
    SInfer -> Lam x mv (freezeBound i ann) $ freezeBound (i + 1) body
freezeBound i (Pi c mv ann body) =
  Pi
    (case typingModeVal @m of SInfer -> c; SCheck -> c)
    mv
    (freezeBound i ann)
    (freezeBound (i + 1) body)
freezeBound i (Sigma c mv ann body) =
  Sigma
    (case typingModeVal @m of SInfer -> c; SCheck -> c)
    mv
    (freezeBound i ann)
    (freezeBound (i + 1) body)
freezeBound i (Pair c f s) =
  Pair
    (case typingModeVal @m of SInfer -> c; SCheck -> c)
    (freezeBound i f)
    (freezeBound i s)
freezeBound i (Split c scrut2 lN rN b) =
  Split
    (case typingModeVal @m of SInfer -> c; SCheck -> c)
    (freezeBound i scrut2)
    lN
    rN
    $ freezeBound (i + 2) b
freezeBound i (Let NoExtField mv e b) =
  Let NoExtField mv (freezeBound i e) $ freezeBound (i + 1) b
freezeBound i (Record c (RecordFieldTypes flds)) =
  Record (case typingModeVal @m of SInfer -> c; SCheck -> c) $
    RecordFieldTypes $
      map (fmap (freezeBound i)) flds
freezeBound i (MkRecord c (MkRecordFields flds)) =
  case typingModeVal @m of
    SCheck -> MkRecord c $ MkRecordFields $ map (fmap (freezeBound i)) flds
    SInfer -> MkRecord c $ MkRecordFields $ map (fmap (freezeBound i)) flds
freezeBound i (ProjField c e f) =
  ProjField (case typingModeVal @m of SInfer -> c; SCheck -> c) (freezeBound i e) f
freezeBound i (Open NoExtField rc b) =
  Open NoExtField (freezeBound i rc) (freezeBound i b)
freezeBound i (XExpr (Inf e)) = XExpr $ Inf $ freezeBound i e
freezeBound i (Variant c (VariantTags flds)) =
  Variant (case typingModeVal @m of SInfer -> c; SCheck -> c) $
    VariantTags $
      map (fmap (freezeBound i)) flds
freezeBound i (Case c e (CaseAlts alts)) =
  Case
    c
    (freezeBound i e)
    $ CaseAlts
    $ map
      ( fmap $ \(CaseAlt d mv b) ->
          CaseAlt d mv $ freezeBound (i + 1) b
      )
      alts
freezeBound i (Inj c l e) = Inj (case typingModeVal @m of SInfer -> c; SCheck -> c) l $ freezeBound i e

freezeBoundName ::
  forall n m.
  Int ->
  Name (Typing m n) ->
  Name (Typing m ('S n))
freezeBoundName i = \case
  Global e n -> Global e n
  PrimName e n -> PrimName e n
  XName (Local l) -> XName $ Local $ There l
  Bound e j
    | j == i -> XName $ Local Here
    | otherwise -> Bound e j

toOrderedList :: HashMap Text a -> [(Text, a)]
toOrderedList = sortOn fst . HM.toList

data TypingMode = Infer | Check
  deriving (Show, Eq, Ord, Generic, Data)

data STypingMode (m :: TypingMode) where
  SInfer :: STypingMode 'Infer
  SCheck :: STypingMode 'Check

class KnownTypingMode m where
  typingModeVal :: STypingMode m

instance KnownTypingMode 'Infer where
  typingModeVal = SInfer

instance KnownTypingMode 'Check where
  typingModeVal = SCheck

newtype TypingVar n = Local (Ordinal n)
  deriving (Show, Eq, Ord, Generic)

instance VarLike (TypingVar n) where
  varName (Local i) =
    pure $
      Just $
        "<<Local: " <> T.pack (show $ fromOrd i) <> ">>"

{- |
A tag for typing AST in infer/check mode with @n@ local anonymous
variables bound in context.
-}
data Typing (typeMode :: TypingMode) (n :: Lvl)
  deriving (Show, Eq, Ord, Generic, Data)

type Inferable' = Typing 'Infer

type Inferable = Typing 'Infer 'Z

type Checkable' = Typing 'Check

type Checkable = Typing 'Check 'Z

type instance XAnn (Inferable' _) = NoExtField

type instance XAnn (Checkable' _) = NoExtCon

type instance AnnLHS (Typing m n) = Expr (Checkable' n)

type instance AnnRHS (Typing m n) = Expr (Checkable' n)

type instance XStar (Inferable' _) = NoExtField

type instance XStar (Checkable' _) = NoExtCon

type instance XVar (Inferable' _) = NoExtField

type instance XVar (Checkable' _) = NoExtCon

type instance XName (Typing _ n) = TypingVar n

type instance XGlobal (Typing _ _) = NoExtField

type instance XBound (Typing _ _) = NoExtField

type instance XPrimName (Typing _ _) = NoExtField

type instance XApp (Inferable' _) = NoExtField

type instance XApp (Checkable' _) = NoExtCon

type instance AppLHS (Typing _ n) = Expr (Inferable' n)

type instance AppRHS (Typing _ n) = Expr (Checkable' n)

type instance XLam (Typing _ _) = NoExtField

type instance LamBindName (Typing m _) = AlphaName

type instance LamBindType (Inferable' n) = Expr (Checkable' n)

type instance LamBindType (Checkable' n) = Maybe (Expr (Checkable' n))

type instance LamBody (Typing m n) = Expr (Typing m n)

type instance XPi (Inferable' _) = NoExtField

type instance XPi (Checkable' _) = NoExtCon

type instance PiVarName (Typing _ _) = AlphaName

type instance PiVarType (Typing _ n) = Expr (Checkable' n)

type instance PiRHS (Typing _ n) = Expr (Checkable' n)

type instance XSigma (Inferable' _) = NoExtField

type instance XSigma (Checkable' _) = NoExtCon

type instance SigmaVarName (Typing _ _) = AlphaName

type instance SigmaVarType (Typing _ n) = Expr (Checkable' n)

type instance SigmaBody (Typing _ n) = Expr (Checkable' n)

type instance XPair (Inferable' _) = NoExtCon

type instance XPair (Checkable' _) = NoExtField

type instance PairFst (Typing _ n) = Expr (Checkable' n)

type instance PairSnd (Typing _ n) = Expr (Checkable' n)

type instance XSplit (Inferable' _) = NoExtCon

type instance XSplit (Checkable' _) = NoExtField

type instance SplitScrutinee (Typing _ n) = Expr (Inferable' n)

type instance SplitFstName (Typing _ _) = AlphaName

type instance SplitSndName (Typing _ _) = AlphaName

type instance SplitBody (Typing _ n) = Expr (Checkable' n)

type instance XLet (Typing _ _) = NoExtField

type instance LetName (Typing _ _) = AlphaName

type instance LetRHS (Typing _ n) = Expr (Inferable' n)

type instance LetBody (Typing e n) = Expr (Typing e n)

type instance XRecord (Inferable' _) = NoExtField

type instance XRecord (Checkable' _) = NoExtCon

type instance RecordFieldType (Typing _ n) = Expr (Checkable' n)

type instance XProjField (Inferable' _) = NoExtField

type instance XProjField (Checkable' _) = NoExtCon

type instance ProjFieldRecord (Typing _ n) = Expr (Inferable' n)

type instance XMkRecord (Typing _ _) = NoExtField

type instance RecordField (Typing m n) = Expr (Typing m n)

type instance XOpen (Typing m n) = NoExtField

type instance OpenRecord (Typing m n) = Expr (Inferable' n)

type instance OpenBody (Typing m n) = Expr (Typing m n)

type instance XVariant (Typing 'Infer _) = NoExtField

type instance XVariant (Typing 'Check _) = NoExtCon

type instance VariantArgType (Typing p n) = Expr (Checkable' n)

type instance XInj (Inferable' n) = NoExtCon

type instance XInj (Checkable' n) = NoExtField

type instance InjArg (Typing e n) = Expr (Typing e n)

type instance XCase (Typing _ _) = NoExtField

type instance CaseArg (Typing _ n) = Expr (Inferable' n)

type instance XCaseAlt (Typing m _) = NoExtField

type instance CaseAltVarName (Typing _ _) = AlphaName

type instance CaseAltBody (Typing m n) = Expr (Typing m n)

type instance XExpr (Typing m n) = XExprTyping m n

data XExprTyping m n where
  Inf :: Expr (Inferable' n) -> XExprTyping 'Check n

deriving instance Show (XExprTyping m n)

deriving instance Eq (XExprTyping m n)

deriving instance Ord (XExprTyping m n)

instance Pretty PrettyEnv (XExprTyping m n) where
  pretty (Inf e) = pretty e
