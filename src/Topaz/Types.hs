{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Topaz.Types
  ( Elem(..)
  ) where

data Elem (rs :: [k]) (r :: k) where
  ElemHere :: Elem (r ': rs) r
  ElemThere :: Elem rs r -> Elem (s ': rs) r
