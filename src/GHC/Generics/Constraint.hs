{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module GHC.Generics.Constraint (FieldC, GFieldC) where

import Data.Kind
import GHC.Generics
import GHC.TypeLits

type FieldC :: (Type -> Constraint) -> Type -> Constraint
class (Generic a, GFieldC c a (Rep a)) => FieldC c a

instance (Generic a, GFieldC c a (Rep a)) => FieldC c a

type GFieldC :: (k -> Constraint) -> k -> (k -> Type) -> Constraint
type family GFieldC c a f where
  -- GFieldC c a (K1 i a) = ()
  GFieldC c a (K1 i b) = (c b)
  GFieldC c a (M1 i x f) = GFieldC c a f
  GFieldC c a (l :*: r) = (GFieldC c a l, GFieldC c a r)
  GFieldC c a (l :+: r) = (GFieldC c a l, GFieldC c a r)
  GFieldC c a U1 = ()
  GFieldC c a V1 = ()
  GFieldC c a f = TypeError ('Text "Unhandled case: " ':<>: 'ShowType f)
