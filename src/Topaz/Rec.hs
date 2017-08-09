{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -Wall #-}

module Topaz.Rec
  ( Rec(..)
  , map
  , traverse
  , traverse_
  , zipWith
  , foldMap
  , foldMap1
  ) where

import Prelude hiding (map,zipWith,foldMap,traverse)
import Data.Exists
import Data.Type.Equality
import Data.Type.Coercion
import Data.Foldable (foldrM)
import Data.Proxy (Proxy(..))
import Foreign.Ptr (castPtr,plusPtr)
import Foreign.Storable (Storable(..))
import Data.Semigroup (Semigroup)
import Data.Hashable (Hashable(..))
import qualified Data.Semigroup as SG
import qualified Data.Vector as V
import qualified Data.Aeson as AE
import qualified Data.Aeson.Types as AET

data Rec :: (k -> *) -> [k] -> * where
  RecNil :: Rec f '[]
  RecCons :: f r -> Rec f rs -> Rec f (r ': rs)

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

instance EqForall f => Eq (Rec f as) where
  (==) = eqForall

instance HashableForall f => HashableForall (Rec f) where
  hashWithSaltForall s0 = go s0 where
    go :: Int -> Rec f rs -> Int
    go !s x = case x of
      RecNil -> s
      RecCons b bs -> go (hashWithSaltForall s b) bs

instance HashableForall f => Hashable (Rec f as) where
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

instance EqForall f => EqForall (Rec f) where
  eqForall RecNil RecNil = True
  eqForall (RecCons a as) (RecCons b bs) =
    eqForall a b && eqForall as bs

instance OrdForall f => Ord (Rec f as) where
  compare = compareForall

instance OrdForall f => OrdForall (Rec f) where
  compareForall RecNil RecNil = EQ
  compareForall (RecCons a as) (RecCons b bs) =
    mappend (compareForall a b) (compareForall as bs)

instance SemigroupForall f => Semigroup (Rec f as) where
  (<>) = zipWith sappendForall

instance (MonoidForall f, Reify as) => Monoid (Rec f as) where
  mempty = map memptyForall (singListToRec reify)
  mappend = zipWith sappendForall

instance MonoidForall f => MonoidForall (Rec f) where
  memptyForall SingListNil = RecNil
  memptyForall (SingListCons s ss) = RecCons (memptyForall s) (memptyForall ss)

instance SemigroupForall f => SemigroupForall (Rec f) where
  sappendForall = zipWith sappendForall

instance ToJSONForall f => AE.ToJSON (Rec f as) where
  toJSON = toJSONForall

instance ToJSONForall f => ToJSONForall (Rec f) where
  toJSONForall = AE.toJSON . go
    where
    go :: forall g xs. ToJSONForall g => Rec g xs -> [AE.Value]
    go RecNil = []
    go (RecCons x xs) = toJSONForall x : go xs

instance (FromJSONForall f, Reify as) => AE.FromJSON (Rec f as) where
  parseJSON = parseJSONForall reify

instance FromJSONForall f => FromJSONForall (Rec f) where
  parseJSONForall s0 = AE.withArray "Rec" $ \vs -> do
    let go :: SingList as -> Int -> AET.Parser (Rec f as)
        go SingListNil !ix = if V.length vs == ix
          then return RecNil
          else fail "too many elements in array"
        go (SingListCons s ss) !ix = if ix < V.length vs
          then do
            r <- parseJSONForall s (vs V.! ix)
            rs <- go ss (ix + 1)
            return (RecCons r rs)
          else fail "not enough elements in array"
    go s0 0

instance StorableForall f => StorableForall (Rec f) where
  sizeOfFunctorForall RecNil = 0
  sizeOfFunctorForall (RecCons r rs) =
    sizeOfFunctorForall r + sizeOfFunctorForall rs
  sizeOfForall _ SingListNil = 0
  sizeOfForall _ (SingListCons s ss) =
    sizeOfForall (Proxy :: Proxy f) s + sizeOfForall (Proxy :: Proxy (Rec f)) ss
  peekForall SingListNil _ = return RecNil
  peekForall (SingListCons s ss) ptr = do
    r <- peekForall s (castPtr ptr)
    rs <- peekForall ss (plusPtr ptr (sizeOfForall (Proxy :: Proxy f) s))
    return (RecCons r rs)
  pokeForall _ RecNil = return ()
  pokeForall ptr (RecCons r rs) = do
    pokeForall (castPtr ptr) r
    pokeForall (plusPtr ptr (sizeOfFunctorForall r)) rs

instance (StorableForall f, Reify as) => Storable (Rec f as) where
  sizeOf _ = sizeOfForall (Proxy :: Proxy (Rec f)) (reify :: SingList as)
  alignment _ = sizeOf (undefined :: Rec f as)
  poke = pokeForall
  peek = peekForall (reify :: SingList as)

instance FromJSONExists f => FromJSONExists (Rec f) where
  parseJSONExists = AE.withArray "Rec" $ \vs -> 
    foldrM go (Exists RecNil) vs
    where
    go :: forall g. FromJSONExists g => AE.Value -> Exists (Rec g) -> AET.Parser (Exists (Rec g))
    go v (Exists rs) = do
      Exists r <- parseJSONExists v :: AET.Parser (Exists g)
      return (Exists (RecCons r rs))

singListToRec :: SingList as -> Rec Sing as
singListToRec SingListNil = RecNil
singListToRec (SingListCons r rs) = RecCons r (singListToRec rs)

map :: (forall x. f x -> g x) -> Rec f as -> Rec g as
map _ RecNil = RecNil
map f (RecCons x xs) = RecCons (f x) (map f xs)

zipWith :: (forall x. f x -> g x -> h x) -> Rec f rs -> Rec g rs -> Rec h rs
zipWith _ RecNil RecNil = RecNil
zipWith f (RecCons a as) (RecCons b bs) =
  RecCons (f a b) (zipWith f as bs)

-- | Map each element of a record to a monoid and combine the results.
foldMap :: forall f m rs. Monoid m
  => (forall x. f x -> m)
  -> Rec f rs
  -> m
foldMap f = go mempty
  where
  go :: forall ss. m -> Rec f ss -> m
  go !m record = case record of
    RecNil -> m
    RecCons r rs -> go (mappend m (f r)) rs
  {-# INLINABLE go #-}
{-# INLINE foldMap #-}

foldMap1 :: forall f m r rs. Semigroup m
  => (forall x. f x -> m)
  -> Rec f (r ': rs)
  -> m
foldMap1 f (RecCons b bs) = go (f b) bs
  where
  go :: forall ss. m -> Rec f ss -> m
  go !m record = case record of
    RecNil -> m
    RecCons r rs -> go (m SG.<> (f r)) rs
  {-# INLINABLE go #-}
{-# INLINE foldMap1 #-}

traverse
  :: Applicative h
  => (forall x. f x -> h (g x))
  -> Rec f rs
  -> h (Rec g rs)
traverse _ RecNil = pure RecNil
traverse f (RecCons x xs) = RecCons <$> f x <*> traverse f xs
{-# INLINABLE traverse #-}

traverse_
  :: Applicative h
  => (forall x. f x -> h b)
  -> Rec f rs
  -> h ()
traverse_ _ RecNil = pure ()
traverse_ f (RecCons x xs) = f x *> traverse_ f xs
{-# INLINABLE traverse_ #-}

