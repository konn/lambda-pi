module Data.Bifunctor.Utils (firstA, module Data.Bitraversable, secondA) where

import Data.Bitraversable

firstA :: (Bitraversable t, Applicative f) => (a -> f a') -> t a b -> f (t a' b)
{-# INLINE firstA #-}
firstA = (`bitraverse` pure)

secondA :: (Bitraversable t, Applicative f) => (b -> f b') -> t a b -> f (t a b')
{-# INLINE secondA #-}
secondA = bitraverse pure
