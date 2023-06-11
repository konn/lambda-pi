{-# LANGUAGE RankNTypes #-}

module Control.Lens.Plated.Extra where

import Control.Lens
import Control.Lens.Plated
import Control.Monad ((>=>))

topDownMOf :: Monad m => Traversal' a a -> (a -> m a) -> a -> m a
topDownMOf t f = go
  where
    {-# INLINE go #-}
    go = f >=> mapMOf t go

topDownM :: (Monad m, Plated a) => (a -> m a) -> a -> m a
topDownM = topDownMOf plate

topDownHoistMOf :: Monad m => Traversal' a a -> (a -> m (a, m a -> m a)) -> a -> m a
topDownHoistMOf t f = go
  where
    {-# INLINE go #-}
    go =
      f >=> \(x, h) ->
        mapMOf t (h . go) x

topDownHoistM :: (Monad m, Plated a) => (a -> m (a, m a -> m a)) -> a -> m a
topDownHoistM = topDownHoistMOf plate
