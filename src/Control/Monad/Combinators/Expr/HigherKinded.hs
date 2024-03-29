{-# LANGUAGE GHC2021 #-}
{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
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
import Control.Monad.Reader (ReaderT (..))
import Data.Bifunctor.Biff (Biff (..))
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

infixr 1 ~=>

(~=>) :: k a -> f (g a) -> DSum k (Compose f g)
l ~=> r = l :=> Compose r

asumDMapWithKey :: Alternative g => (forall v. k v -> f v -> g a) -> DMap k f -> g a
asumDMapWithKey f = getAlt . getConst . DMap.traverseWithKey (fmap (Const . Alt) . f)

dsumParsers :: Alternative m => ParserDict t m f -> m (DSum t f)
dsumParsers = asumDMapWithKey $ \tv (Compose p) ->
  (tv :=>) <$> p

readNextTerm ::
  forall k f m v e s.
  (MonadParsec e s m, MonadFail m, GCompare k) =>
  CastFunctions k f ->
  k v ->
  ParserDict k m f ->
  (forall z. k z -> f z -> m (f v)) ->
  m (f v)
readNextTerm casters kv terms f = try $ do
  kx :=> fx <- dsumParsers terms
  let (Alt comps, Alt simpls) =
        foldMap'
          ( \(kx' :=> Biff toFx') ->
              let simpl =
                    foldMap' (\Refl -> Alt $ pure $ toFx' fx) $
                      geq kx' kv
                  comp = Alt $ try $ f kx' $ toFx' fx
               in (comp, simpl)
          )
          $ getCasters kx casters
  comps <|> label "fallback term" simpls

-- | Lookup casters, including identity
getCasters :: GCompare k => k v -> CastFunctions k f -> [DSum k (Biff (->) f f v)]
getCasters kx casters =
  DMap.toList $
    DMap.insert kx (Biff id) $
      maybe mempty getCompose $
        DMap.lookup kx casters

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
    go tv = readNextTerm casters tv terms $ \tx fx ->
      parseFixR casters terms fixR tx tv fx
        <|> parseFixL casters terms fixL tx tv fx
        <|> parseFixN casters terms fixN tx tv fx

    (fixN, fixL, fixR) =
      foldMap'
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

preCasters ::
  GCompare k =>
  k v ->
  CastFunctions k f ->
  DMap k (Flip (Biff (->) f f) v)
preCasters kv casters =
  DMap.insert kv (Flip (Biff id)) $
    DMap.mapMaybe
      ( getCompose
          >>> DMap.lookup kv
          >>> fmap Flip
      )
      casters

parserOf ::
  forall k m f x.
  (GCompare k, Alternative m, MonadFail m, GShow k) =>
  CastFunctions k f ->
  k x ->
  ParserDict k m f ->
  m (f x)
parserOf casters kv =
  let casts' = preCasters kv casters
   in runReaderT
        $ alaf
          Alt
          foldMap'
          ( \(kx :=> Flip (Biff toFv)) ->
              ReaderT $
                maybe
                  (fail $ "Parser not found for: " <> gshow kx)
                  (fmap toFv . getCompose)
                  . DMap.lookup kx
          )
        $ DMap.toList casts'

parseFixN ::
  (GCompare k, MonadParsec e s m, MonadFail m, GShow k) =>
  CastFunctions k f ->
  ParserDict k m f ->
  InfixInOutDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixN casters terms (InfixInOutDic ndic) frm dst x =
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
                    ( \(HInfixLike tr p) -> do
                        f <- p
                        f x $ parserOf casters tr terms
                    )
                    ents
              )
              $ DMap.lookup dst dic
        )
        $ DMap.lookup frm fixN

parseFixL ::
  forall k m f from to e s.
  (GCompare k, MonadParsec e s m, MonadFail m, GShow k) =>
  CastFunctions k f ->
  ParserDict k m f ->
  InfixLDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixL casters terms (InfixLDic ldic) = goL
  where
    fixL = DMap.mapWithKey (const $ _Wrapped %~ DLNE.toNonEmpty) ldic
    goL :: k x -> k y -> f x -> m (f y)
    goL frm dst x =
      maybe
        ( fail $
            "parseFixL: key `"
              <> gshow frm
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
                  !z <- f x $ parserOf casters tr terms
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
      let dests' = DMap.toList $ preCasters dst casters
       in maybe
            ( fail $
                "parseFixR: outer key `"
                  <> gshow frm
                  <> "' not found in: "
                  <> show (DMap.keys fixR)
                  <> "; all term parsers: "
                  <> show (DMap.keys terms)
            )
            ( \(Compose (Compose dic)) ->
                alaf
                  Alt
                  foldMap'
                  ( \(dst' :=> Flip (Biff toDst)) ->
                      maybe
                        ( fail $
                            "parseFixN: inner key `"
                              <> gshow dst'
                              <> "' not found in: "
                              <> show (DMap.keys dic)
                              <> "; all term parsers: "
                              <> show (DMap.keys terms)
                        )
                        ( alaf
                            Alt
                            foldMap1
                            ( \(HInfixLike tr p) -> do
                                f <- p
                                fmap toDst $
                                  f x $
                                    readNextTerm casters tr terms (`goR` tr)
                            )
                            . getCompose
                        )
                        $ DMap.lookup dst' dic
                  )
                  dests'
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
