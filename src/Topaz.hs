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

module Topaz
  ( Rec(..)
  , unreifyList
  ) where

import Data.Exists
import Data.Type.Equality
import Data.Type.Coercion
import Data.Foldable (foldrM)
import Data.Proxy (Proxy(..))
import Foreign.Ptr (castPtr,plusPtr)
import Foreign.Storable (Storable(..))
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

instance (MonoidForall f, Implicit as) => Monoid (Rec f as) where
  mempty = rmap memptyForall (singListToRec implicit)
  mappend = rzipWith sappendForall

instance MonoidForall f => MonoidForall (Rec f) where
  memptyForall SingListNil = RecNil
  memptyForall (SingListCons s ss) = RecCons (memptyForall s) (memptyForall ss)

instance SemigroupForall f => SemigroupForall (Rec f) where
  sappendForall = rzipWith sappendForall

instance ToJSONForall f => AE.ToJSON (Rec f as) where
  toJSON = toJSONForall

instance ToJSONForall f => ToJSONForall (Rec f) where
  toJSONForall = AE.toJSON . go
    where
    go :: forall g xs. ToJSONForall g => Rec g xs -> [AE.Value]
    go RecNil = []
    go (RecCons x xs) = toJSONForall x : go xs

instance (FromJSONForall f, Implicit as) => AE.FromJSON (Rec f as) where
  parseJSON = parseJSONForall implicit

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

instance (StorableForall f, Implicit as) => Storable (Rec f as) where
  sizeOf _ = sizeOfForall (Proxy :: Proxy (Rec f)) (implicit :: SingList as)
  alignment _ = sizeOf (undefined :: Rec f as)
  poke = pokeForall
  peek = peekForall (implicit :: SingList as)

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

rmap :: (forall x. f x -> g x) -> Rec f as -> Rec g as
rmap _ RecNil = RecNil
rmap f (RecCons x xs) = RecCons (f x) (rmap f xs)

rzipWith :: (forall x. f x -> g x -> h x) -> Rec f rs -> Rec g rs -> Rec h rs
rzipWith _ RecNil RecNil = RecNil
rzipWith f (RecCons a as) (RecCons b bs) =
  RecCons (f a b) (rzipWith f as bs)

unreifyList :: forall (as :: [k]) b. Unreify k => SingList as -> (Implicit as => b) -> b
unreifyList SingListNil b = b
unreifyList (SingListCons s ss) b = unreify s (unreifyList ss b)

class Implicit a where
  implicit :: Sing a

instance Implicit '[] where
  implicit = SingListNil

instance (Reify a, Implicit as) => Implicit (a ': as) where
  implicit = SingListCons reify implicit
