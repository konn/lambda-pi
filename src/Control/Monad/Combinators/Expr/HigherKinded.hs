{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
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
  CastFunctions,
  Compose (..),
  (~=>),
  parserOf,
) where

import Control.Applicative (Alternative)
import Control.Applicative.Combinators
import Control.Arrow ((>>>))
import Control.Lens
import Control.Monad
import Data.Bifunctor.Biff (Biff (..))
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DLNE
import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum
import Data.FMList (FMList)
import Data.FMList qualified as FML
import Data.Foldable
import Data.Functor.Compose (Compose (..))
import Data.Functor.Product (Product (..))
import Data.GADT.Compare (GCompare, GEq, geq)
import Data.GADT.Show
import Data.Kind (Type)
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import Data.Monoid (Alt (..))
import Data.Semigroup.Foldable (foldMap1)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Some
import Text.Megaparsec (MonadParsec (..))

type HOperator :: forall {k}. (k -> Type) -> (Type -> Type) -> (k -> Type) -> Type
data HOperator k m f where
  InfixN
    , InfixL
    , InfixR ::
    k l -> k r -> k v -> m (f l -> m (f r) -> m (f v)) -> HOperator k m f

type CastFunctions k f = DMap k (Compose (DMap k) (Biff (->) f f))

makeHExprParser ::
  (MonadPlus m, GCompare k, MonadFail m, GShow k, MonadParsec e s m) =>
  Set (Some k) ->
  CastFunctions k f ->
  ParserDict k m f ->
  [[HOperator k m f]] ->
  ParserDict k m f
makeHExprParser vs casts = foldl' (addPrecLevel vs casts)

data HOpInOut k m f l v where
  HInfixLike :: k r -> m (f l -> m (f r) -> m (f v)) -> HOpInOut k m f l v

newtype InfixInOutDic k m f
  = InfixInOutDic
      (DMap k (Compose (Compose (DMap k) (Compose DNonEmpty)) (HOpInOut k m f)))

singletonInfixInOutDic :: k l -> k v -> HOpInOut k m f l v -> InfixInOutDic k m f
singletonInfixInOutDic frm dst =
  InfixInOutDic . DMap.singleton frm . Compose . Compose . DMap.singleton dst . Compose . DLNE.singleton

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

infixr 1 ~=>, :~=>

(~=>) :: k a -> f (g a) -> DSum k (Compose f g)
l ~=> r = l :=> Compose r

{-# COMPLETE (:~=>) #-}

pattern (:~=>) :: k a -> f (g a) -> DSum k (Compose f g)
pattern l :~=> r = l :=> Compose r

asumDMapWithKey :: Alternative g => (forall v. k v -> f v -> g a) -> DMap k f -> g a
asumDMapWithKey f = getAlt . getConst . DMap.traverseWithKey (fmap (Const . Alt) . f)

dsumParsers :: Alternative m => ParserDict t m f -> m (DSum t f)
dsumParsers = asumDMapWithKey $ \tv (Compose p) ->
  (tv :=>) <$> p

asumMapAtLast ::
  forall k f m v e s.
  (MonadParsec e s m, GCompare k) =>
  CastFunctions k f ->
  k v ->
  ParserDict k m f ->
  (forall z. k z -> f z -> m (f v)) ->
  m (f v)
asumMapAtLast casters kv terms f = do
  -- FIXME: Can we do this more efficiently (i.e. w/o singleton comparison or re-parsing)?
  kx :=> fx <- dsumParsers terms
  let dests =
        DMap.insert kx (Biff id) $
          maybe mempty getCompose $
            DMap.lookup kx casters
  let simples :: FMList (f v)
      compounds :: FMList (m (f v))
      (compounds, simples) =
        flip foldMap' (DMap.toList dests) $ \(kx' :=> Biff tofx') ->
          let simpl =
                foldMap (\Refl -> FML.singleton $ tofx' fx) $
                  geq kv kx'
           in (FML.singleton $ f kx fx, simpl)
  alaf Alt foldMap' try compounds <|> alaf Alt foldMap' pure simples

addPrecLevel ::
  forall k m f e s.
  (GCompare k, MonadFail m, GShow k, MonadParsec e s m) =>
  Set (Some k) ->
  CastFunctions k f ->
  ParserDict k m f ->
  [HOperator k m f] ->
  ParserDict k m f
addPrecLevel targs casters terms ops =
  DMap.fromList $ map (\(Some t) -> t ~=> go t) $ Set.toList targs
  where
    go :: forall v. k v -> m (f v)
    go tv = asumMapAtLast casters tv terms $ \tx fx ->
      parseFixR casters terms fixR tx tv fx
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

weightSome :: GEq k => k v -> DSum k f -> (Int, Some k)
weightSome kv (ku :=> _) =
  case geq kv ku of
    Just Refl -> (100, Some ku)
    Nothing -> (0, Some ku)

parserOf ::
  (GCompare k, Alternative m, MonadFail m, GShow k) =>
  k x ->
  ParserDict k m f ->
  m (f x)
parserOf tv = maybe (fail $ "Parser not found for: " <> gshow tv) getCompose . DMap.lookup tv

parseFixN ::
  (GCompare k, MonadParsec e s m, MonadFail m, GShow k) =>
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
              <> gshow frm
              <> "' not found in: "
              <> show (DMap.keys fixN)
              <> "; all term parsers: "
              <> show (DMap.keys terms)
        )
        ( \(Compose (Compose dic)) ->
            maybe
              ( fail $
                  "parseFixN: inner key `"
                    <> gshow dst
                    <> "' not found in: "
                    <> show (DMap.keys dic)
                    <> "; all term parsers: "
                    <> show (DMap.keys terms)
              )
              ( \(Compose ents) ->
                  alaf
                    Alt
                    foldMap1
                    ( \(HInfixLike tr p) -> try $ do
                        f <- p
                        f x $ parserOf tr terms
                    )
                    ents
              )
              $ DMap.lookup dst dic
        )
        $ DMap.lookup frm fixN

parseFixL ::
  forall k m f from to e s.
  (GCompare k, MonadParsec e s m, MonadFail m, GShow k) =>
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
              ( getCompose >>> \(kret :=> HInfixLike tr p) -> try $ do
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
  forall k m f from to e s.
  (GCompare k, MonadParsec e s m, MonadFail m, GShow k) =>
  CastFunctions k f ->
  ParserDict k m f ->
  InfixInOutDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixR casters terms (InfixInOutDic rdic) = goR
  where
    fixR = DMap.mapWithKey (const $ _Wrapped . _Wrapped %~ DMap.mapWithKey (const $ _Wrapped %~ DLNE.toNonEmpty)) rdic
    goR :: k x -> k y -> f x -> m (f y)
    goR !frm !dst !x =
      maybe
        ( fail $
            "parseFixR: outer key `"
              <> gshow frm
              <> "' not found in: "
              <> show (DMap.keys fixR)
              <> "; all term parsers: "
              <> show (DMap.keys terms)
        )
        ( \(Compose (Compose dic)) ->
            maybe
              ( fail $
                  "parseFixN: inner key `"
                    <> gshow dst
                    <> "' not found in: "
                    <> show (DMap.keys dic)
                    <> "; all term parsers: "
                    <> show (DMap.keys terms)
              )
              ( \(Compose ents) ->
                  alaf
                    Alt
                    foldMap1
                    ( \(HInfixLike tr p) -> try $ do
                        f <- p
                        f x $ asumMapAtLast casters tr terms $ \ky !fy -> do
                          goR ky tr fy
                    )
                    ents
              )
              $ DMap.lookup dst dic
        )
        $ DMap.lookup frm fixR

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
