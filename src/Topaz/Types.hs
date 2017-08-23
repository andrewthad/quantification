{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Topaz.Types
  ( Elem(..)
  , type (++)
  ) where

data Elem (rs :: [k]) (r :: k) where
  ElemHere :: Elem (r ': rs) r
  ElemThere :: Elem rs r -> Elem (s ': rs) r

type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  (a ': as) ++ bs = a ': (as ++ bs)
infixr 5 ++
