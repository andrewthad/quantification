module Data.Monoid.Lifted
  ( Semigroup1(..)
  , Monoid1(..)
  , append1
  , empty1
  ) where

import Control.Applicative
import Data.Functor.Compose
import Data.Functor.Identity
import Data.HashMap.Strict (HashMap)
import Data.Hashable (Hashable)
import Data.Map.Strict (Map)
import Data.Monoid
import Data.Proxy (Proxy(..))
import Data.Semigroup (Semigroup)
import qualified Data.Functor.Product as FP
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.Semigroup as SG

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

-- | Disagrees with 'Semigroup' instance for 'Map'
instance Ord k => Semigroup1 (Map k) where
  liftAppend = M.unionWith

instance Ord k => Monoid1 (Map k) where
  liftEmpty _ = M.empty

-- | Disagrees with 'Semigroup' instance for 'HashMap'
instance (Hashable k, Eq k) => Semigroup1 (HashMap k) where
  liftAppend = HM.unionWith

instance (Hashable k, Eq k) => Monoid1 (HashMap k) where
  liftEmpty _ = HM.empty

instance Semigroup1 [] where
  liftAppend _ = (++)

instance Monoid1 [] where
  liftEmpty _ = []

instance Semigroup1 Identity where
  liftAppend f (Identity a) (Identity b) = Identity (f a b)

instance Monoid1 Identity where
  liftEmpty = Identity

instance (Semigroup1 f, Semigroup1 g) => Semigroup1 (FP.Product f g) where
  liftAppend f (FP.Pair a1 b1) (FP.Pair a2 b2) = FP.Pair (liftAppend f a1 a2) (liftAppend f b1 b2)

instance (Monoid1 f, Monoid1 g) => Monoid1 (FP.Product f g) where
  liftEmpty a = FP.Pair (liftEmpty a) (liftEmpty a)

instance Semigroup1 Dual where
  liftAppend f (Dual a) (Dual b) = Dual (f b a)

instance Monoid1 Dual where
  liftEmpty a = Dual a

instance Semigroup a => Semigroup1 ((,) a) where
  liftAppend f (a1,b1) (a2,b2) = (a1 SG.<> a2, f b1 b2)

instance (Semigroup a, Monoid a) => Monoid1 ((,) a) where
  liftEmpty b = (mempty,b)

instance Semigroup1 Proxy where
  liftAppend _ _ _ = Proxy

instance Monoid1 Proxy where
  liftEmpty _ = Proxy

instance Semigroup1 ((->) a) where
  liftAppend combine f g a = combine (f a) (g a)

instance Monoid1 ((->) a) where
  liftEmpty b _ = b

