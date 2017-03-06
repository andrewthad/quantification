{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE CPP #-}
module Data.Exists where

import Data.Proxy (Proxy)
import Data.Type.Equality ((:~:)(Refl))
import Control.Applicative (Const(..))
import Data.Aeson (ToJSON(..),FromJSON(..))
import Data.Hashable (Hashable(..))
import Data.Text (Text)
import qualified Data.Aeson.Types as Aeson
import qualified Text.Read as R
import qualified Text.Read.Lex as R

#if MIN_VERSION_aeson(1,0,0) 
import qualified Data.Aeson.Encoding as Aeson
import Data.Aeson (ToJSONKey(..),FromJSONKey(..),
  ToJSONKeyFunction(..),FromJSONKeyFunction(..))
#endif

-- newtype Exists (f :: k -> *) = Exists { runExists :: forall r. (forall a. f a -> r) -> r }

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

class (OrdForall f, EqForallPoly f) => OrdForallPoly f where
  compareForallPoly :: f a -> f b -> Ordering

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

