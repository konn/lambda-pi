{-# LANGUAGE BangPatterns #-}

module Data.List.NonEmpty.Utils (
  module Data.List.NonEmpty,
  unsnoc,
) where

import Control.Arrow ((>>>))
import qualified Data.DList as DL
import Data.List.NonEmpty

unsnoc :: NonEmpty a -> ([a], a)
unsnoc = uncons >>> uncurry (go mempty)
  where
    go !acc x Nothing = (DL.toList acc, x)
    go !acc x (Just (y :| ys)) = go (acc `DL.snoc` x) y (nonEmpty ys)
