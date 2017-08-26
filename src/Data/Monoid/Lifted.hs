module Data.Monoid.Lifted
  ( Semigroup1(..)
  , Monoid1(..)
  , append1
  , empty1
  ) where

import Data.Functor.Identity
import Data.Functor.Compose
import Data.Functor.Product
import Data.Map.Strict (Map)
import Control.Applicative
import Data.Semigroup (Semigroup)
import qualified Data.Semigroup as SG
import qualified Data.Map.Strict as M

-- | Laws for this typeclass:
--
-- * @liftAppend f a (liftAppend f b c) = liftAppend f (liftAppend f a b) c@
class Semigroup1 f where
  liftAppend :: (a -> a -> a) -> f a -> f a -> f a

append1 :: (Semigroup1 f, Semigroup a) => f a -> f a -> f a
append1 = liftAppend (SG.<>)

-- | Laws for this typeclass:
--
-- * @liftAppend f a (liftEmpty mempty) = a@
class Semigroup1 f => Monoid1 f where
  liftEmpty :: a -> f a

empty1 :: (Monoid1 f, Monoid a) => f a
empty1 = liftEmpty mempty

instance Semigroup1 Maybe where
  liftAppend _ Nothing Nothing = Nothing
  liftAppend _ a@(Just _) Nothing = a
  liftAppend _ Nothing a@(Just _) = a
  liftAppend f (Just a) (Just b) = Just (f a b)

instance (Semigroup1 f, Semigroup1 g) => Semigroup1 (Compose f g) where
  liftAppend f (Compose a) (Compose b) = Compose ((liftAppend (liftAppend f)) a b)

instance (Monoid1 f, Monoid1 g) => Monoid1 (Compose f g) where
  liftEmpty a = Compose (liftEmpty (liftEmpty a))

instance Semigroup1 IO where
  liftAppend = liftA2

instance Monoid1 IO where
  liftEmpty = pure

instance Ord k => Semigroup1 (Map k) where
  liftAppend = M.unionWith

instance Semigroup1 [] where
  liftAppend _ = (++)

instance Monoid1 [] where
  liftEmpty _ = []

instance Semigroup1 Identity where
  liftAppend f (Identity a) (Identity b) = Identity (f a b)

instance Monoid1 Identity where
  liftEmpty = Identity

instance (Semigroup1 f, Semigroup1 g) => Semigroup1 (Product f g) where
  liftAppend f (Pair a1 b1) (Pair a2 b2) = Pair (liftAppend f a1 a2) (liftAppend f b1 b2)

instance (Monoid1 f, Monoid1 g) => Monoid1 (Product f g) where
  liftEmpty a = Pair (liftEmpty a) (liftEmpty a)



