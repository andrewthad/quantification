{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Topaz.Types
  ( Elem(..)
  , Rec(..)
  -- , BiRec(..)
  , NestRec(..)
  , Fix(..)
  , HFix(..)
  , Nest(..)
  , EqHetero(..)
  , TestEqualityHetero(..)
  , Nat(..)
  , SingNat(..)
  , Vector(..)
  , type (++)
  ) where

import Control.Applicative (liftA2)
import Data.Exists
import Data.Hashable (Hashable(..))
import Data.Kind (Type)
import Data.Monoid.Lifted (Semigroup1(..), Monoid1(..), append1)
import Data.Proxy (Proxy(..))
import Data.Type.Coercion
import Data.Type.Equality
import Foreign.Ptr (castPtr,plusPtr)
import Foreign.Storable (Storable(..))

import qualified Data.Semigroup as SG

data Nat = Succ Nat | Zero

data SingNat :: Nat -> Type where
  SingZero :: SingNat 'Zero
  SingSucc :: SingNat n -> SingNat ('Succ n)

type instance Sing = SingNat

data Vector :: Nat -> Type -> Type where
  VectorNil :: Vector 'Zero a
  VectorCons :: a -> Vector n a -> Vector ('Succ n) a

instance Eq a => Eq (Vector n a) where
  VectorNil == VectorNil = True
  VectorCons a as == VectorCons b bs = a == b && as == bs

data Elem (rs :: [k]) (r :: k) where
  ElemHere :: Elem (r ': rs) r
  ElemThere :: Elem rs r -> Elem (s ': rs) r

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)
infixr 5 ++

data Rec :: forall (k :: Type). (k -> Type) -> [k] -> Type where
  RecNil :: Rec f '[]
  RecCons :: f r -> Rec f rs -> Rec f (r ': rs)

-- data BiRec :: (k -> Type) -> (j -> Type) -> [k] -> [j] -> Type where
--   BiRec :: Rec f ks -> Rec g js -> BiRec f g ks js

data NestRec :: forall (k :: Type). (k -> Type) -> Nest k -> Type where
  NestRec :: Rec f rs -> Rec (NestRec f) ns -> NestRec f ('Nest ns rs)

data Nest a = Nest [Nest a] [a]
newtype Fix f = Fix (f (Fix f))
newtype HFix h a = HFix (h (HFix h) a)

instance Semigroup1 f => Semigroup (Fix f) where
  Fix a <> Fix b = Fix (append1 a b)

instance Monoid1 f => Monoid (Fix f) where
  mempty = Fix (liftEmpty mempty)
  mappend = (SG.<>)

-- Think of a better name for this typeclass
class EqHetero h where
  eqHetero :: (forall x. f x -> f x -> Bool) -> h f a -> h f a -> Bool

instance EqHetero h => EqForall (HFix h) where
  eqForall (HFix a) (HFix b) = eqHetero eqForall a b 

instance EqHetero h => Eq (HFix h a) where
  (==) = eqForall

class TestEqualityHetero h where
  testEqualityHetero :: (forall x y. f x -> f y -> Maybe (x :~: y)) -> h f a -> h f b -> Maybe (a :~: b)

instance TestEqualityHetero h => TestEquality (HFix h) where
  testEquality (HFix a) (HFix b) = testEqualityHetero testEquality a b

instance TestEquality f => TestEquality (Rec f) where
  testEquality RecNil RecNil = Just Refl
  testEquality (RecCons x xs) (RecCons y ys) = do
    Refl <- testEquality x y
    Refl <- testEquality xs ys
    Just Refl
  testEquality _ _ = Nothing

instance TestCoercion f => TestCoercion (Rec f) where
  testCoercion RecNil RecNil = Just Coercion
  testCoercion (RecCons x xs) (RecCons y ys) = do
    Coercion <- testCoercion x y
    Coercion <- testCoercion xs ys
    Just Coercion
  testCoercion _ _ = Nothing

instance HashableForall f => HashableForall (Rec f) where
  hashWithSaltForall s0 = go s0 where
    go :: Int -> Rec f rs -> Int
    go !s x = case x of
      RecNil -> s
      RecCons b bs -> go (hashWithSaltForall s b) bs

instance (EqForall f, HashableForall f) => Hashable (Rec f as) where
  hashWithSalt = hashWithSaltForall

instance ShowForall f => ShowForall (Rec f) where
  showsPrecForall p x = case x of
    RecCons v vs -> showParen (p > 10)
      $ showString "RecCons "
      . showsPrecForall 11 v
      . showString " "
      . showsPrecForall 11 vs
    RecNil -> showString "RecNil"

instance ShowForall f => Show (Rec f as) where
  showsPrec = showsPrecForall

instance ShowForeach f => ShowForeach (Rec f) where
  showsPrecForeach SingListNil _ RecNil = showString "RecNil"
  showsPrecForeach (SingListCons s ss) p (RecCons v vs) = showParen (p > 10)
    $ showString "RecCons "
    . showsPrecForeach s 11 v
    . showString " "
    . showsPrecForeach ss 11 vs

instance EqForall f => Eq (Rec f as) where
  (==) = eqForall

instance EqForall f => EqForall (Rec f) where
  eqForall RecNil RecNil = True
  eqForall (RecCons a as) (RecCons b bs) =
    eqForall a b && eqForall as bs

instance EqForeach f => EqForeach (Rec f) where
  eqForeach SingListNil RecNil RecNil = True
  eqForeach (SingListCons s ss) (RecCons a as) (RecCons b bs) =
    eqForeach s a b && eqForeach ss as bs

instance EqForallPoly f => EqForallPoly (Rec f) where
  eqForallPoly RecNil RecNil = WitnessedEqualityEqual
  eqForallPoly RecNil (RecCons _ _) = WitnessedEqualityUnequal
  eqForallPoly (RecCons _ _) RecNil = WitnessedEqualityUnequal
  eqForallPoly (RecCons x xs) (RecCons y ys) = case eqForallPoly x y of
    WitnessedEqualityUnequal -> WitnessedEqualityUnequal
    WitnessedEqualityEqual -> case eqForallPoly xs ys of
      WitnessedEqualityUnequal -> WitnessedEqualityUnequal
      WitnessedEqualityEqual -> WitnessedEqualityEqual

instance OrdForall f => Ord (Rec f as) where
  compare = compareForall

instance OrdForall f => OrdForall (Rec f) where
  compareForall RecNil RecNil = EQ
  compareForall (RecCons a as) (RecCons b bs) =
    mappend (compareForall a b) (compareForall as bs)

instance OrdForeach f => OrdForeach (Rec f) where
  compareForeach SingListNil RecNil RecNil = EQ
  compareForeach (SingListCons s ss) (RecCons a as) (RecCons b bs) =
    mappend (compareForeach s a b) (compareForeach ss as bs)


instance SemigroupForall f => Semigroup (Rec f as) where
  (<>) = recZipWith appendForall

instance SemigroupForeach f => SemigroupForeach (Rec f) where
  appendForeach SingListNil RecNil RecNil = RecNil
  appendForeach (SingListCons s ss) (RecCons x xs) (RecCons y ys) =
    RecCons (appendForeach s x y) (appendForeach ss xs ys)

instance MonoidForeach f => MonoidForeach (Rec f) where
  emptyForeach SingListNil = RecNil
  emptyForeach (SingListCons s ss) = RecCons (emptyForeach s) (emptyForeach ss)

instance SemigroupForall f => SemigroupForall (Rec f) where
  appendForall = recZipWith appendForall

instance StorableForeach f => StorableForeach (Rec f) where
  sizeOfForeach _ SingListNil = 0
  sizeOfForeach _ (SingListCons s ss) =
    sizeOfForeach (Proxy :: Proxy f) s + sizeOfForeach (Proxy :: Proxy (Rec f)) ss
  peekForeach SingListNil _ = return RecNil
  peekForeach (SingListCons s ss) ptr = do
    r <- peekForeach s (castPtr ptr)
    rs <- peekForeach ss (plusPtr ptr (sizeOfForeach (Proxy :: Proxy f) s))
    return (RecCons r rs)
  pokeForeach _ _ RecNil = return ()
  pokeForeach (SingListCons s ss) ptr (RecCons r rs) = do
    pokeForeach s (castPtr ptr) r
    pokeForeach ss (plusPtr ptr (sizeOfForeach (Proxy :: Proxy f) s)) rs

instance (StorableForeach f, Reify as) => Storable (Rec f as) where
  sizeOf _ = sizeOfForeach (Proxy :: Proxy (Rec f)) (reify :: SingList as)
  alignment _ = sizeOf (undefined :: Rec f as)
  poke = pokeForeach (reify :: SingList as)
  peek = peekForeach (reify :: SingList as)

instance BinaryForeach f => BinaryForeach (Rec f) where
  putForeach SingListNil RecNil = return ()
  putForeach (SingListCons s ss) (RecCons r rs) = do
    putForeach s r
    putForeach ss rs
  getForeach SingListNil = return RecNil
  getForeach (SingListCons s ss) =
    liftA2 RecCons (getForeach s) (getForeach ss)

recZipWith :: (forall x. f x -> g x -> h x) -> Rec f rs -> Rec g rs -> Rec h rs
recZipWith _ RecNil RecNil = RecNil
recZipWith f (RecCons a as) (RecCons b bs) =
  RecCons (f a b) (recZipWith f as bs)

