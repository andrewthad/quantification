{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-| Data types and type classes for working with existentially quantified
    values. In the event that Quantified Class Constraints ever land in GHC,
    this package will be considered obsolete. The benefit that most of the
    typeclasses in this module provide is that they help populate the instances
    of 'Exists'.
-}

module Data.Exists
  ( -- * Data Types
    Exists(..)
  , Exists2(..)
  , Exists3(..)
    -- * Type Classes
  , EqForall(..)
  , EqForallPoly(..)
  , OrdForall(..)
  , OrdForallPoly(..)
  , ShowForall(..)
  , ReadForall(..)
  , EnumForall(..)
  , BoundedForall(..)
  , SemigroupForall(..)
  , MonoidForall(..)
  , HashableForall(..)
  , PathPieceForall(..)
  , FromJSONForall(..)
  , ToJSONForall(..)
#if MIN_VERSION_aeson(1,0,0) 
  , ToJSONKeyForall(..)
  , FromJSONKeyForall(..)
#endif
    -- * Higher Rank Classes
  , EqForall2(..)
  , EqForallPoly2(..)
    -- * Functions
  , showsForall
  , showForall
  , defaultEqForallPoly
  , defaultCompareForallPoly
  ) where

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(Refl),TestEquality(..))
import Control.Applicative (Const(..))
import Data.Aeson (ToJSON(..),FromJSON(..))
import Data.Hashable (Hashable(..))
import Data.Text (Text)
import Data.Functor.Sum (Sum(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Compose (Compose(..))
import GHC.Int (Int(..))
import GHC.Prim (dataToTag#)
import qualified Data.Aeson.Types as Aeson
import qualified Text.Read as R
import qualified Web.PathPieces as PP

#if MIN_VERSION_aeson(1,0,0) 
import qualified Data.Aeson.Encoding as Aeson
import Data.Aeson (ToJSONKey(..),FromJSONKey(..),
  ToJSONKeyFunction(..),FromJSONKeyFunction(..))
#endif

-- newtype Exists (f :: k -> *) = Exists { runExists :: forall r. (forall a. f a -> r) -> r }

-- | Hide a type parameter.
data Exists (f :: k -> *) = forall a. Exists !(f a)

data Exists2 (f :: k -> j -> *) = forall a b. Exists2 !(f a b)

data Exists3 (f :: k -> j -> l -> *) = forall a b c. Exists3 !(f a b c)

#if MIN_VERSION_aeson(1,0,0) 
data ToJSONKeyFunctionForall f
  = ToJSONKeyTextForall !(forall a. f a -> Text) !(forall a. f a -> Aeson.Encoding' Text)
  | ToJSONKeyValueForall !(forall a. f a -> Aeson.Value) !(forall a. f a -> Aeson.Encoding)
#endif

class EqForall f where
  eqForall :: f a -> f a -> Bool

class EqForall f => OrdForall f where
  compareForall :: f a -> f a -> Ordering

class EqForall f => EqForallPoly f where
  eqForallPoly :: f a -> f b -> Bool
  default eqForallPoly :: TestEquality f => f a -> f b -> Bool
  eqForallPoly = defaultEqForallPoly

-- the default method does not work if your data type is a newtype wrapper
-- over a function, but that should not really ever happen.
class (OrdForall f, EqForallPoly f) => OrdForallPoly f where
  compareForallPoly :: f a -> f b -> Ordering
  default compareForallPoly :: TestEquality f => f a -> f b -> Ordering
  compareForallPoly = defaultCompareForallPoly

class ShowForall f where
  showsPrecForall :: Int -> f a -> ShowS

showsForall :: ShowForall f => f a -> ShowS
showsForall = showsPrecForall 0

showForall :: ShowForall f => f a -> String
showForall x = showsForall x ""

class ReadForall f where
  readPrecForall :: R.ReadPrec (Exists f)

class EqForall2 f where
  eqForall2 :: f a b -> f a b -> Bool

class EqForallPoly2 f where
  eqForallPoly2 :: f a b -> f c d -> Bool

class HashableForall f where
  hashWithSaltForall :: Int -> f a -> Int

#if MIN_VERSION_aeson(1,0,0) 
class ToJSONKeyForall f where
  toJSONKeyForall :: ToJSONKeyFunctionForall f

class FromJSONKeyForall f where
  fromJSONKeyForall :: FromJSONKeyFunction (Exists f)
#endif

class ToJSONForall f where
  toJSONForall :: f a -> Aeson.Value

class FromJSONForall f where
  parseJSONForall :: Aeson.Value -> Aeson.Parser (Exists f)

class EnumForall f where
  toEnumForall :: Int -> Exists f
  fromEnumForall :: f a -> Int

class BoundedForall f where
  minBoundForall :: Exists f
  maxBoundForall :: Exists f

class PathPieceForall f where
  fromPathPieceForall :: Text -> Maybe (Exists f)
  toPathPieceForall :: f a -> Text

class SemigroupForall f where
  sappendForall :: f a -> f a -> f a

class SemigroupForall f => MonoidForall f where
  memptyForall :: f a

--------------------
-- Instances Below
--------------------

instance EqForall Proxy where
  eqForall _ _ = True

instance OrdForall Proxy where
  compareForall _ _ = EQ

instance ShowForall Proxy where
  showsPrecForall = showsPrec

instance ReadForall Proxy where
  readPrecForall = fmap Exists R.readPrec 

instance SemigroupForall Proxy where
  sappendForall _ _ = Proxy 

instance MonoidForall Proxy where
  memptyForall = Proxy

instance EqForall ((:~:) a) where
  eqForall Refl Refl = True

instance EqForall2 (:~:) where
  eqForall2 Refl Refl = True



instance Eq a => EqForall (Const a) where
  eqForall (Const x) (Const y) = x == y

instance Eq a => EqForallPoly (Const a) where
  eqForallPoly (Const x) (Const y) = x == y

instance Ord a => OrdForall (Const a) where
  compareForall (Const x) (Const y) = compare x y

instance Ord a => OrdForallPoly (Const a) where
  compareForallPoly (Const x) (Const y) = compare x y

instance Hashable a => HashableForall (Const a) where
  hashWithSaltForall s (Const a) = hashWithSalt s a


#if MIN_VERSION_aeson(1,0,0) 
-- I need to get rid of the ToJSONForall and FromJSONForall constraints
-- on these two instances.
instance (ToJSONKeyForall f, ToJSONForall f) => ToJSONKey (Exists f) where
  toJSONKey = case toJSONKeyForall of
    ToJSONKeyTextForall t e -> ToJSONKeyText (\(Exists a) -> t a) (\(Exists a) -> e a)
    ToJSONKeyValueForall v e -> ToJSONKeyValue (\x -> case x of Exists a -> v a) (\(Exists a) -> e a)

instance (FromJSONKeyForall f, FromJSONForall f) => FromJSONKey (Exists f) where
  fromJSONKey = fromJSONKeyForall
#endif

instance EqForallPoly f => Eq (Exists f) where
  Exists a == Exists b = eqForallPoly a b

instance EqForallPoly2 f => Eq (Exists2 f) where
  Exists2 a == Exists2 b = eqForallPoly2 a b

instance OrdForallPoly f => Ord (Exists f) where
  compare (Exists a) (Exists b) = compareForallPoly a b

instance HashableForall f => Hashable (Exists f) where
  hashWithSalt s (Exists a) = hashWithSaltForall s a

instance ToJSONForall f => ToJSON (Exists f) where
  toJSON (Exists a) = toJSONForall a

instance FromJSONForall f => FromJSON (Exists f) where
  parseJSON v = parseJSONForall v

instance ShowForall f => Show (Exists f) where
  showsPrec p (Exists a) = showParen 
    (p >= 11) 
    (showString "Exists " . showsPrecForall 11 a)

instance ReadForall f => Read (Exists f) where
  readPrec = R.parens $ R.prec 10 $ do
    R.Ident "Exists" <- R.lexP
    R.step readPrecForall
    
instance EnumForall f => Enum (Exists f) where
  fromEnum (Exists x) = fromEnumForall x
  toEnum = toEnumForall

instance BoundedForall f => Bounded (Exists f) where
  minBound = minBoundForall
  maxBound = maxBoundForall

instance PathPieceForall f => PP.PathPiece (Exists f) where
  toPathPiece (Exists f) = toPathPieceForall f
  fromPathPiece = fromPathPieceForall

instance (EqForall f, EqForall g) => EqForall (Product f g) where
  eqForall (Pair f1 g1) (Pair f2 g2) = eqForall f1 f2 && eqForall g1 g2

instance (EqForallPoly f, EqForallPoly g) => EqForallPoly (Product f g) where
  eqForallPoly (Pair f1 g1) (Pair f2 g2) = eqForallPoly f1 f2 && eqForallPoly g1 g2

instance (OrdForall f, OrdForall g) => OrdForall (Product f g) where
  compareForall (Pair f1 g1) (Pair f2 g2) = mappend (compareForall f1 f2) (compareForall g1 g2)

instance (OrdForallPoly f, OrdForallPoly g) => OrdForallPoly (Product f g) where
  compareForallPoly (Pair f1 g1) (Pair f2 g2) = mappend (compareForallPoly f1 f2) (compareForallPoly g1 g2)

instance (ShowForall f, ShowForall g) => ShowForall (Product f g) where
  showsPrecForall p (Pair f g) = showParen 
    (p >= 11) 
    (showString "Pair " . showsPrecForall 11 f . showChar ' ' . showsPrecForall 11 g)

instance (EqForall f) => EqForall (Compose f g) where
  eqForall (Compose x) (Compose y) = eqForall x y

instance (EqForallPoly f) => EqForallPoly (Compose f g) where
  eqForallPoly (Compose x) (Compose y) = eqForallPoly x y

instance (EqForall f, EqForall g) => EqForall (Sum f g) where
  eqForall (InL f1) (InL f2) = eqForall f1 f2
  eqForall (InR f1) (InR f2) = eqForall f1 f2
  eqForall (InR _) (InL _) = False
  eqForall (InL _) (InR _) = False

instance (OrdForall f, OrdForall g) => OrdForall (Sum f g) where
  compareForall (InL f1) (InL f2) = compareForall f1 f2
  compareForall (InR f1) (InR f2) = compareForall f1 f2
  compareForall (InR _) (InL _) = GT
  compareForall (InL _) (InR _) = LT

defaultCompareForallPoly :: (TestEquality f, OrdForall f) => f a -> f b -> Ordering
defaultCompareForallPoly a b = case testEquality a b of
  Nothing -> compare (getTagBox a) (getTagBox b)
  Just Refl -> compareForall a b

defaultEqForallPoly :: (TestEquality f, EqForall f) => f a -> f b -> Bool
defaultEqForallPoly x y = case testEquality x y of
  Nothing -> False
  Just Refl -> eqForall x y

getTagBox :: a -> Int
getTagBox !x = I# (dataToTag# x)
{-# INLINE getTagBox #-}

