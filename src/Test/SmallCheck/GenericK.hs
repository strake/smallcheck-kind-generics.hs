{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Test.SmallCheck.GenericK where

import Control.Applicative
import Data.Kind (Type)
import Data.Type.Equality
import GHC.Generics (C)
import Generics.Kind hiding ((:~:))
import Type.Reflection (Typeable, typeRep)

import Test.SmallCheck.Series

genericSeries :: ∀ m a x q . (GenericK a, GSerial m (RepK a) x) => q x -> Series m a
genericSeries _ = toK <$> (gSeries :: Series m (RepK a x))

class GSerial m (f :: LoT k -> Type) (x :: LoT k) where
    gSeries :: Series m (f x)

instance GSerial m U1 x where
    gSeries = pure U1
instance GSerial m V1 x where
    gSeries = empty
instance (Monad m, GSerial m f x, GSerial m g x) => GSerial m (f :+: g) x where
    gSeries = (L1 <$> gSeries) \/ (R1 <$> gSeries)
instance (Monad m, GSerial m f x, GSerial m g x) => GSerial m (f :*: g) x where
    gSeries = (:*:) <$> gSeries <~> gSeries
instance (Typeable i, GSerial m f x) => GSerial m (M1 i c f) x where
    gSeries = ($ M1 <$> gSeries) $ case testEquality typeRep typeRep :: Maybe (i :~: C) of
        Just _ -> decDepth; _ -> id
instance (Serial m (Interpret t x)) => GSerial m (Field t) x where
    gSeries = Field <$> series
instance (∀ (t :: k) . GSerial m f (t :&&: x)) => GSerial m (Exists k f) x where
    gSeries = Exists <$> gSeries
instance (Interpret c x, GSerial m f x) => GSerial m (c :=>: f) x where
    gSeries = SuchThat <$> gSeries
