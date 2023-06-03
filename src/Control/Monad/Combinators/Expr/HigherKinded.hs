{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Monad.Combinators.Expr.HigherKinded (
  HOperator (..),
  infixN,
  infixL,
  infixR,
  makeHExprParser,
  ParserDict,
  Compose (..),
  (~=>),
  parserOf,
) where

import Control.Applicative (Alternative)
import Control.Applicative.Combinators
import Control.Arrow ((>>>))
import Control.Lens
import Control.Monad
import Data.Bifunctor.Flip (Flip (..))
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DLNE
import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum
import Data.Foldable
import Data.Functor.Compose (Compose (..))
import Data.GADT.Compare (GCompare, geq)
import Data.GADT.Show
import Data.Kind (Type)
import Data.Monoid (Alt (..))
import Data.Semigroup.Foldable (foldMap1)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Some
import Debug.Trace qualified as DT

type HOperator :: forall {k}. (k -> Type) -> (Type -> Type) -> (k -> Type) -> Type
data HOperator k m f where
  InfixN
    , InfixL
    , InfixR ::
    k l -> k r -> k v -> m (f l -> m (f r) -> m (f v)) -> HOperator k m f

makeHExprParser ::
  (MonadPlus m, GCompare k, MonadFail m, GShow k) =>
  Set (Some k) ->
  ParserDict k m f ->
  [[HOperator k m f]] ->
  ParserDict k m f
makeHExprParser vs = foldl' (addPrecLevel vs)

data HOpInOut k m f l v where
  HInfixLike :: k r -> m (f l -> m (f r) -> m (f v)) -> HOpInOut k m f l v

asumDMapWithKey :: Alternative g => (forall v. k v -> f v -> g a) -> DMap k f -> g a
asumDMapWithKey f = getAlt . getConst . DMap.traverseWithKey (fmap (Const . Alt) . f)

dsumParsers :: Alternative m => ParserDict t m f -> m (DSum t f)
dsumParsers = asumDMapWithKey $ \tv (Compose p) ->
  (tv :=>) <$> p

newtype InfixInOutDic k m f
  = InfixInOutDic
      (DMap k (Compose (Compose (DMap k) (Compose DNonEmpty)) (Flip (HOpInOut k m f))))

singletonInfixInOutDic :: k l -> k v -> HOpInOut k m f l v -> InfixInOutDic k m f
singletonInfixInOutDic frm dst =
  InfixInOutDic . DMap.singleton dst . Compose . Compose . DMap.singleton frm . Compose . DLNE.singleton . Flip

instance GCompare k => Semigroup (InfixInOutDic k m f) where
  InfixInOutDic l <> InfixInOutDic r =
    InfixInOutDic $
      DMap.unionWithKey
        ( const $ \(Compose (Compose ls)) (Compose (Compose rs)) ->
            Compose $ Compose $ DMap.unionWithKey (const (<>)) ls rs
        )
        l
        r

instance GCompare k => Monoid (InfixInOutDic k m f) where
  mempty = InfixInOutDic mempty

newtype InfixLDic k m f = InfixLDic (DMap k (Compose DNonEmpty (Compose (DSum k) (HOpInOut k m f))))

singletonInfixL :: k l -> k v -> HOpInOut k m f l v -> InfixLDic k m f
singletonInfixL src dst =
  InfixLDic . DMap.singleton src . Compose . DLNE.singleton . Compose . (dst :=>)

instance GCompare k => Semigroup (InfixLDic k m f) where
  InfixLDic l <> InfixLDic r =
    InfixLDic $
      DMap.unionWithKey
        ( const $ \(Compose ls) (Compose rs) ->
            Compose $ ls <> rs
        )
        l
        r

instance GCompare k => Monoid (InfixLDic k m f) where
  mempty = InfixLDic mempty

type ParserDict k m f = DMap k (Compose m f)

infixr 1 ~=>

(~=>) :: k a -> f (g a) -> DSum k (Compose f g)
l ~=> r = l :=> Compose r

addPrecLevel ::
  forall k m f.
  (GCompare k, MonadPlus m, MonadFail m, GShow k) =>
  Set (Some k) ->
  ParserDict k m f ->
  [HOperator k m f] ->
  ParserDict k m f
addPrecLevel targs terms ops =
  DMap.fromList $
    map (\(Some t) -> t ~=> go t) $
      Set.toList targs
  where
    someTerm = dsumParsers terms
    go :: forall v. k v -> m (f v)
    go tv = do
      tx :=> fx <- ((tv :=>) <$> parserOf tv terms) <|> someTerm
      let withFallback p =
            case geq tv tx of
              Just Refl -> p <|> pure fx
              Nothing -> p

      withFallback $
        parseFixR terms fixR tx tv fx
          <|> parseFixL terms fixL tx tv fx
          <|> parseFixN terms fixN tx tv fx

    (fixN, fixL, fixR) =
      foldMap
        ( \case
            InfixN l r v p ->
              ( singletonInfixInOutDic l v $ HInfixLike r p
              , mempty
              , mempty
              )
            InfixR l r v p ->
              ( mempty
              , mempty
              , singletonInfixInOutDic l v $ HInfixLike r p
              )
            InfixL l r v p ->
              ( mempty
              , singletonInfixL l v $ HInfixLike r p
              , mempty
              )
        )
        ops

parserOf ::
  (GCompare k, Alternative m, MonadFail m, GShow k) =>
  k x ->
  ParserDict k m f ->
  m (f x)
parserOf tv = maybe (fail $ "Parser not found for: " <> gshow tv) getCompose . DMap.lookup tv

parseFixN ::
  (GCompare k, MonadPlus m, MonadFail m, GShow k) =>
  ParserDict k m f ->
  InfixInOutDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixN terms (InfixInOutDic ndic) frm dst x =
  let fixN = DMap.mapWithKey (const $ _Wrapped . _Wrapped %~ DMap.mapWithKey (const $ _Wrapped %~ DLNE.toNonEmpty)) ndic
   in maybe
        ( fail $
            "parseFixN: outer key `"
              <> gshow dst
              <> "' not found in: "
              <> show (DMap.keys fixN)
              <> "; all term parsers: "
              <> show (DMap.keys terms)
        )
        ( \(Compose (Compose dic)) ->
            maybe
              ( fail $
                  "parseFixN: inner key `"
                    <> gshow frm
                    <> "' not found in: "
                    <> show (DMap.keys dic)
                    <> "; all term parsers: "
                    <> show (DMap.keys terms)
              )
              ( \(Compose ents) ->
                  alaf
                    Alt
                    foldMap1
                    ( \(Flip (HInfixLike tr p)) -> do
                        f <- p
                        f x $ parserOf tr terms
                    )
                    ents
              )
              $ DMap.lookup frm dic
        )
        $ DMap.lookup dst fixN

parseFixL ::
  forall k m f from to.
  (GCompare k, MonadPlus m, MonadFail m, GShow k) =>
  ParserDict k m f ->
  InfixLDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixL terms (InfixLDic ldic) = goL
  where
    fixL = DMap.mapWithKey (const $ _Wrapped %~ DLNE.toNonEmpty) ldic
    goL :: k x -> k y -> f x -> m (f y)
    goL frm dst x =
      maybe
        ( fail $
            "parseFixL: key `"
              <> gshow dst
              <> "' not found in: "
              <> show (DMap.keys fixL)
              <> "; all term parsers: "
              <> show (DMap.keys terms)
        )
        ( getCompose
            >>> alaf
              Alt
              foldMap1
              ( getCompose >>> \(kret :=> HInfixLike tr p) -> do
                  f <- p
                  !z <- f x $ parserOf tr terms
                  let
                    fall q = case geq kret dst of
                      Just Refl -> q <|> pure z
                      Nothing -> q
                  fall $ goL kret dst z
              )
        )
        $ DMap.lookup frm fixL

parseFixR ::
  forall k m f from to.
  (GCompare k, MonadPlus m, MonadFail m, GShow k) =>
  ParserDict k m f ->
  InfixInOutDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixR terms (InfixInOutDic rdic) = goR
  where
    fixR = DMap.mapWithKey (const $ _Wrapped . _Wrapped %~ DMap.mapWithKey (const $ _Wrapped %~ DLNE.toNonEmpty)) rdic
    someTerm = dsumParsers terms
    goR :: k x -> k y -> f x -> m (f y)
    goR frm dst x =
      maybe
        ( fail $
            "parseFixR: outer key `"
              <> gshow dst
              <> "' not found in: "
              <> show (DMap.keys fixR)
              <> "; all term parsers: "
              <> show (DMap.keys terms)
        )
        ( \(Compose (Compose dic)) ->
            maybe
              ( fail $
                  "parseFixN: inner key `"
                    <> gshow frm
                    <> "' not found in: "
                    <> show (DMap.keys dic)
                    <> "; all term parsers: "
                    <> show (DMap.keys terms)
              )
              ( \(Compose ents) ->
                  alaf
                    Alt
                    foldMap1
                    ( \(Flip (HInfixLike tr p)) -> do
                        f <- p

                        f x $ do
                          ky :=> !fy <- someTerm
                          let defY q = case geq ky tr of
                                Just Refl -> q <|> pure fy
                                Nothing -> q
                          defY $ goR ky tr fy
                    )
                    ents
              )
              $ DMap.lookup frm dic
        )
        $ DMap.lookup dst fixR

infixN
  , infixL
  , infixR ::
    Functor m =>
    k l ->
    k r ->
    k v ->
    m (f l -> f r -> f v) ->
    HOperator k m f
infixN l r v mf = InfixN l r v $ mf <&> \f fl mfr -> f fl <$> mfr
infixL l r v mf = InfixL l r v $ mf <&> \f fl mfr -> f fl <$> mfr
infixR l r v mf = InfixR l r v $ mf <&> \f fl mfr -> f fl <$> mfr
