{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}

module Topaz.Rec
  ( Rec(..)
  , map
  , append
  , traverse
  , traverse_
  , zipWith
  , foldMap
  , foldMap1
    -- * Access
  , get
  , put
  , gets
  , puts
    -- * Conversion
  , fromSingList
  , toSingList
  ) where

import Prelude hiding (map,zipWith,foldMap,traverse)
import Topaz.Types (Elem(..),type (++),Rec(..))
import Data.Exists
import Data.Semigroup (Semigroup)
import qualified Data.Semigroup as SG

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

get :: Elem rs r -> Rec f rs -> f r
get ElemHere (RecCons r _) = r
get (ElemThere ix) (RecCons _ rs) = get ix rs

put :: Elem rs r -> f r -> Rec f rs -> Rec f rs
put ElemHere r' (RecCons _ rs) = RecCons r' rs
put (ElemThere ix) r' (RecCons r rs) = RecCons r (put ix r' rs)

gets :: Rec (Elem rs) ss -> Rec f rs -> Rec f ss
gets ixs rec = map (\e -> get e rec) ixs

puts :: Rec (Elem rs) ss -> Rec f rs -> Rec f ss -> Rec f rs
puts RecNil rs _ = rs
puts (RecCons ix ixs) rs (RecCons s ss) = put ix s (puts ixs rs ss)

append :: Rec f as -> Rec f bs -> Rec f (as ++ bs)
append RecNil ys = ys
append (RecCons x xs) ys = RecCons x (append xs ys)

fromSingList :: SingList as -> Rec Sing as
fromSingList SingListNil = RecNil
fromSingList (SingListCons r rs) = RecCons r (fromSingList rs)

toSingList :: Rec Sing as -> SingList as
toSingList RecNil = SingListNil
toSingList (RecCons r rs) = SingListCons r (toSingList rs)

