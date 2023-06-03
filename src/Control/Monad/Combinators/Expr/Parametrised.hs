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

module Control.Monad.Combinators.Expr.Parametrised (
  HOperator (..),
  makeHExprParser,
  Compose (..),
) where

import Control.Applicative (Alternative)
import Control.Applicative.Combinators
import Control.Arrow ((>>>))
import Control.Lens
import Control.Monad
import Data.Bifunctor.Flip (Flip (..))
import Data.DList (DList)
import Data.DList qualified as DL
import Data.Dependent.Map (DMap)
import Data.Dependent.Map qualified as DMap
import Data.Dependent.Sum
import Data.Foldable
import Data.Functor.Compose (Compose (..))
import Data.GADT.Compare (GCompare, geq)
import Data.Monoid (Alt (..))

data HOperator k m f where
  InfixN
    , InfixL
    , InfixR ::
    k l -> k r -> k v -> m (f l -> f r -> f v) -> HOperator k m f

makeHExprParser ::
  (MonadPlus m, GCompare k) =>
  TermParsers k m f ->
  [[HOperator k m f]] ->
  TermParsers k m f
makeHExprParser = foldl' addPrecLevel

data HOpInOut k m f l v where
  HInfixLike :: k r -> m (f l -> f r -> f v) -> HOpInOut k m f l v

asumDMapWithKey :: Alternative g => (forall v. k v -> f v -> g a) -> DMap k f -> g a
asumDMapWithKey f = getAlt . getConst . DMap.traverseWithKey (fmap (Const . Alt) . f)

dsumParsers :: Alternative m => TermParsers t m f -> m (DSum t f)
dsumParsers = asumDMapWithKey $ \tv (Compose p) ->
  (tv :=>) <$> p

newtype InfixInOutDic k m f
  = InfixInOutDic
      (TermParsers k (Compose (DMap k) (Compose DList)) (Flip (HOpInOut k m f)))

singletonInfixInOutDic :: k l -> k v -> HOpInOut k m f l v -> InfixInOutDic k m f
singletonInfixInOutDic frm dst =
  InfixInOutDic . DMap.singleton dst . Compose . Compose . DMap.singleton frm . Compose . DL.singleton . Flip

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

newtype InfixLDic k m f = InfixLDic (DMap k (Compose DList (Compose (DSum k) (HOpInOut k m f))))

singletonInfixL :: k l -> k v -> HOpInOut k m f l v -> InfixLDic k m f
singletonInfixL src dst =
  InfixLDic . DMap.singleton src . Compose . DL.singleton . Compose . (dst :=>)

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

type TermParsers k m f = DMap k (Compose m f)

addPrecLevel ::
  forall k m f.
  (GCompare k, MonadPlus m) =>
  TermParsers k m f ->
  [HOperator k m f] ->
  TermParsers k m f
addPrecLevel terms ops = DMap.mapWithKey (const . Compose . go) terms
  where
    someTerm = dsumParsers terms
    go :: forall v. k v -> m (f v)
    go tv = do
      tx :=> fx <- someTerm
      let fallBack = case geq tv tx of
            Just Refl -> pure fx
            Nothing -> empty

      choice
        [ parseFixR terms fixR tx tv fx
        , parseFixL terms fixL tx tv fx
        , parseFixN terms fixN tx tv fx
        , fallBack
        ]

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

termOf :: (GCompare k, Alternative m) => k x -> TermParsers k m f -> m (f x)
termOf tv = maybe empty getCompose . DMap.lookup tv

parseFixN ::
  (GCompare k, Alternative m) =>
  TermParsers k m f ->
  InfixInOutDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixN terms (InfixInOutDic ndic) frm dst x =
  let fixN = DMap.mapWithKey (const $ _Wrapped . _Wrapped %~ DMap.mapWithKey (const $ _Wrapped %~ DL.toList)) ndic
   in maybe
        empty
        ( \(Compose (Compose dic)) ->
            maybe
              empty
              ( \(Compose ents) ->
                  alaf
                    Alt
                    foldMap
                    ( \(Flip (HInfixLike tr p)) -> do
                        f <- p
                        y <- termOf tr terms
                        pure $ f x y
                    )
                    ents
              )
              $ DMap.lookup frm dic
        )
        $ DMap.lookup dst fixN

parseFixL ::
  forall k m f from to.
  (GCompare k, MonadPlus m) =>
  TermParsers k m f ->
  InfixLDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixL terms (InfixLDic ldic) = goL
  where
    fixL = DMap.mapWithKey (const $ _Wrapped %~ DL.toList) ldic
    goL :: k x -> k y -> f x -> m (f y)
    goL frm dst x =
      maybe
        empty
        ( getCompose
            >>> alaf
              Alt
              foldMap
              ( getCompose >>> \(kret :=> HInfixLike tr p) -> do
                  f <- p
                  y <- termOf tr terms
                  let !z = f x y
                      fall = case geq kret dst of
                        Just Refl -> pure z
                        Nothing -> empty
                  goL kret dst z <|> fall
              )
        )
        $ DMap.lookup frm fixL

parseFixR ::
  forall k m f from to.
  (GCompare k, MonadPlus m) =>
  TermParsers k m f ->
  InfixInOutDic k m f ->
  k from ->
  k to ->
  f from ->
  m (f to)
parseFixR terms (InfixInOutDic rdic) = goR
  where
    fixR = DMap.mapWithKey (const $ _Wrapped . _Wrapped %~ DMap.mapWithKey (const $ _Wrapped %~ DL.toList)) rdic
    someTerm = dsumParsers terms
    goR :: k x -> k y -> f x -> m (f y)
    goR frm dst x =
      maybe
        empty
        ( \(Compose (Compose dic)) ->
            maybe
              empty
              ( \(Compose ents) ->
                  alaf
                    Alt
                    foldMap
                    ( \(Flip (HInfixLike tr p)) -> do
                        f <- p
                        ky :=> !fy <- someTerm
                        let defY = case geq ky tr of
                              Just Refl -> pure fy
                              Nothing -> empty
                        y <- goR ky tr fy <|> defY
                        pure $ f x y
                    )
                    ents
              )
              $ DMap.lookup frm dic
        )
        $ DMap.lookup dst fixR
