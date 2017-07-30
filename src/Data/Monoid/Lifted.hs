module Data.Monoid.Lifted
  ( Semigroup1(..)
  ) where

import Data.Functor.Compose

class Semigroup1 f where
  sappend1 :: (a -> a -> a) -> f a -> f a -> f a

instance Semigroup1 Maybe where
  sappend1 _ Nothing Nothing = Nothing
  sappend1 _ a@(Just _) Nothing = a
  sappend1 _ Nothing a@(Just _) = a
  sappend1 f (Just a) (Just b) = Just (f a b)

instance (Semigroup1 f, Semigroup1 g) => Semigroup1 (Compose f g) where
  sappend1 f (Compose a) (Compose b) = Compose ((sappend1 (sappend1 f)) a b)

