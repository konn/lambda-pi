{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Data.Level.Sequence where

import Data.Kind (Type)
import Data.Level

type LSeq :: (Lvl -> Type) -> Lvl -> Type
data LSeq f n where
  LStop :: f 'Z -> LSeq f ('S 'Z)
  LCons :: f n -> LSeq f n -> LSeq f ('S n)
