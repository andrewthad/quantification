{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}

{-# OPTIONS_GHC -Wall #-}

{-| Data types and type classes for working with existentially quantified
    values. When Quantified Class Constraints land in GHC 8.6,
    the @BarForall@ classes will be considered obsolete. When Dependent
    Haskell lands, the @BarForeach@ classes will also be obsolete.
    The benefit that most of the typeclasses in this module provide is
    that they help populate the instances of 'Exists' and @Rec@.
-}

module Data.Exists
  ( -- * Data Types
    Exists(..)
  , Exists2(..)
  , Exists3(..)
  , Some(..)
  , DependentPair(..)
  , WitnessedEquality(..)
  , WitnessedOrdering(..)
  , ApplyForeach(..)
  , ApplyLifted(..)
    -- * Type Classes
  , EqForall(..)
  , EqForallPoly(..)
  , EqForeach(..)
  , OrdForall(..)
  , OrdForallPoly(..)
  , OrdForeach(..)
  , ShowForall(..)
  , ShowForeach(..)
  , ReadExists(..)
  , EnumForall(..)
  , EnumExists(..)
  , BoundedExists(..)
  , SemigroupForall(..)
  , SemigroupForeach(..)
  , MonoidForall(..)
  , MonoidForeach(..)
  , HashableForall(..)
  , HashableForeach(..)
  , PathPieceExists(..)
  , FromJSONForeach(..)
  , FromJSONExists(..)
  , ToJSONForall(..)
  , ToJSONForeach(..)
  , ToJSONKeyFunctionForall(..)
  , FromJSONKeyFunctionForeach(..)
  , ToJSONKeyForall(..)
  , ToJSONKeyForeach(..)
  , FromJSONKeyExists(..)
  , FromJSONKeyForeach(..)
  , StorableForeach(..)
  , StorableForall(..)
  , PrimForall(..)
  , BinaryExists(..)
  , BinaryForeach(..)
    -- * Higher Rank Classes
  , EqForall2(..)
  , EqForallPoly2(..)
  , ShowForall2(..)
  , ShowForeach2(..)
  , BinaryExists2(..)
    -- * More Type Classes
  , Sing
  , SingList(..)
  , SingMaybe(..)
  , Reify(..)
  , Unreify(..)
    -- * Sing Type Classes
  , EqSing(..)
  , OrdSing(..)
  , ShowSing(..)
  , ToJSONSing(..)
  , FromJSONSing(..)
  , ToSing(..)
  , SingKind(..)
    -- * Functions
    -- ** Show
  , showsForall
  , showsForeach
  , showForall
  , showListForall
  , showListForeach
  , showsForall2
  , showForall2
    -- ** Defaulting
  , defaultEqForallPoly
  , defaultCompareForallPoly
  , parseJSONMapForeachKey
  , toJSONMapForeachKey
    -- ** Weakening
  , weakenEquality
  , weakenOrdering
  , strengthenEquality
  , strengthenOrdering
  , strengthenUnequalOrdering
    -- ** Other
  , unreifyList
  ) where

import Control.Applicative (Const(..))
import Data.Aeson (ToJSON(..),FromJSON(..))
import Data.Aeson (ToJSONKey(..),FromJSONKey(..))
import Data.Aeson (ToJSONKeyFunction(..),FromJSONKeyFunction(..))
import Data.Aeson.Internal ((<?>),JSONPathElement(Key,Index))
import Data.Binary (Get,Put,Binary)
import Data.Binary.Lifted (Binary1(..))
import Data.Coerce (coerce)
import Data.Functor.Classes (Eq1(..),Show1(..),Ord1(..),eq1,compare1)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..))
import Data.Functor.Sum (Sum(..))
import Data.Hashable (Hashable(..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import Data.Monoid.Lifted (Semigroup1(..),Monoid1(..),append1,empty1)
import Data.Proxy (Proxy(..))
import Data.Semigroup (Semigroup)
import Data.Text (Text)
import Data.Type.Equality ((:~:)(Refl),TestEquality(..))
import Foreign.Ptr (Ptr)
import GHC.Exts (dataToTag#,State#,Int#,Proxy#,Addr#,ByteArray#,MutableByteArray#)
import GHC.Int (Int(..))

import qualified Data.Aeson.Encoding as Aeson
import qualified Data.Aeson.Encoding.Internal as AEI
import qualified Data.Aeson.Types as Aeson
import qualified Data.Binary as BN
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.Semigroup as SG
import qualified Data.Traversable as TRV
import qualified Data.Vector as V
import qualified Text.Read as R
import qualified Web.PathPieces as PP

-- | Hide a type parameter.
data Exists (f :: k -> Type) = forall a. Exists !(f a)

-- | Hide two type parameters.
data Exists2 (f :: k -> j -> Type) = forall a b. Exists2 !(f a b)

-- | Hide three type parameters.
data Exists3 (f :: k -> j -> l -> Type) = forall a b c. Exists3 !(f a b c)

-- | A pair in which the type of the second element can only
--   be discovered by looking at the first element. The type
--   instance does not enforce this, but all of its typeclass
--   instances make this assumption.
data DependentPair (f :: k -> Type) (g :: k -> Type) =
  forall a. DependentPair (f a) (g a)

-- | A dependent pair in which the first element is a singleton.
data Some (f :: k -> Type) = forall a. Some !(Sing a) !(f a)

data WitnessedEquality (a :: k) (b :: k) where
  WitnessedEqualityEqual :: WitnessedEquality a a
  WitnessedEqualityUnequal :: WitnessedEquality a b

data WitnessedOrdering (a :: k) (b :: k) where
  WitnessedOrderingLT :: WitnessedOrdering a b
  WitnessedOrderingEQ :: WitnessedOrdering a a
  WitnessedOrderingGT :: WitnessedOrdering a b

data ToJSONKeyFunctionForall f
  = ToJSONKeyTextForall !(forall a. f a -> Text) !(forall a. f a -> Aeson.Encoding' Text)
  | ToJSONKeyValueForall !(forall a. f a -> Aeson.Value) !(forall a. f a -> Aeson.Encoding)
data FromJSONKeyFunctionForeach f
  = FromJSONKeyTextParserForeach !(forall a. Sing a -> Text -> Aeson.Parser (f a))
  | FromJSONKeyValueForeach !(forall a. Sing a -> Aeson.Value -> Aeson.Parser (f a))

newtype ApplyLifted f a = ApplyLifted { getApplyLifted :: f a }                         

instance (Semigroup1 f, Semigroup a) => Semigroup (ApplyLifted f a) where  
  (<>) = append1

instance (Monoid1 f, Monoid a) => Monoid (ApplyLifted f a) where
  mempty = empty1 
  mappend = liftAppend mappend

instance (Eq1 f, Eq a) => Eq (ApplyLifted f a) where
  (==) = eq1 

instance (Ord1 f, Ord a) => Ord (ApplyLifted f a) where
  compare = compare1 

instance Semigroup1 f => Semigroup1 (ApplyLifted f) where  
  liftAppend g (ApplyLifted a) (ApplyLifted b) = ApplyLifted (liftAppend g a b)                        

instance Monoid1 f => Monoid1 (ApplyLifted f) where        
  liftEmpty f = ApplyLifted (liftEmpty f)                                        

instance Eq1 f => Eq1 (ApplyLifted f) where
  liftEq f (ApplyLifted a) (ApplyLifted b) = liftEq f a b

instance Ord1 f => Ord1 (ApplyLifted f) where
  liftCompare f (ApplyLifted a) (ApplyLifted b) = liftCompare f a b

-- | This is useful for recovering an instance of a typeclass when
-- we have the pi-quantified variant and a singleton in scope.
newtype ApplyForeach f a = ApplyForeach { getApplyForeach :: f a }

instance (EqForeach f, Reify a) => Eq (ApplyForeach f a) where
  ApplyForeach a == ApplyForeach b = eqForeach reify a b

instance (OrdForeach f, Reify a) => Ord (ApplyForeach f a) where
  compare (ApplyForeach a) (ApplyForeach b) = compareForeach reify a b

instance (ShowForeach f, Reify a) => Show (ApplyForeach f a) where
  showsPrec p (ApplyForeach a) = showParen (p > 10)
    $ showString "ApplyForeach "
    . showsPrecForeach reify 11 a

instance (SemigroupForeach f, Reify a) => Semigroup (ApplyForeach f a) where
  (<>) = appendForeach reify

instance (MonoidForeach f, Reify a) => Monoid (ApplyForeach f a) where
  mempty = emptyForeach reify
  mappend = (SG.<>)

instance (ToJSONForeach f, Reify a) => ToJSON (ApplyForeach f a) where
  toJSON = toJSONForeach reify

instance (FromJSONForeach f, Reify a) => FromJSON (ApplyForeach f a) where
  parseJSON = parseJSONForeach reify

instance EqForeach f => EqForeach (ApplyForeach f) where
  eqForeach s (ApplyForeach a) (ApplyForeach b) = eqForeach s a b

instance OrdForeach f => OrdForeach (ApplyForeach f) where
  compareForeach s (ApplyForeach a) (ApplyForeach b) = compareForeach s a b

instance SemigroupForeach f => SemigroupForeach (ApplyForeach f) where
  appendForeach s (ApplyForeach a) (ApplyForeach b) = ApplyForeach (appendForeach s a b)

instance MonoidForeach f => MonoidForeach (ApplyForeach f) where
  emptyForeach s = ApplyForeach (emptyForeach s)

instance ToJSONForeach f => ToJSONForeach (ApplyForeach f) where
  toJSONForeach s (ApplyForeach x) = toJSONForeach s x

instance FromJSONForeach f => FromJSONForeach (ApplyForeach f) where
  parseJSONForeach s = fmap ApplyForeach . parseJSONForeach s

instance ToJSONKeyForeach f => ToJSONKeyForeach (ApplyForeach f) where
  toJSONKeyForeach = case toJSONKeyForeach of
    ToJSONKeyTextForall f g -> ToJSONKeyTextForall
      (\(Pair s (ApplyForeach x)) -> f (Pair s x))
      (\(Pair s (ApplyForeach x)) -> g (Pair s x))
    ToJSONKeyValueForall f g -> ToJSONKeyValueForall
      (\(Pair s (ApplyForeach x)) -> f (Pair s x))
      (\(Pair s (ApplyForeach x)) -> g (Pair s x))

instance FromJSONKeyForeach f => FromJSONKeyForeach (ApplyForeach f) where
  fromJSONKeyForeach = case fromJSONKeyForeach of
    FromJSONKeyTextParserForeach f -> FromJSONKeyTextParserForeach (\s t -> fmap ApplyForeach (f s t))
    FromJSONKeyValueForeach f -> FromJSONKeyValueForeach (\s t -> fmap ApplyForeach (f s t))

instance (ToJSONKeyForeach f, Reify a) => ToJSONKey (ApplyForeach f a) where
  toJSONKey = case toJSONKeyForeach of
    ToJSONKeyTextForall toText toEnc -> ToJSONKeyText
      (\(ApplyForeach x) -> toText (Pair reify x))
      (\(ApplyForeach x) -> toEnc (Pair reify x))
    ToJSONKeyValueForall toValue toEnc -> ToJSONKeyValue
      (\(ApplyForeach x) -> toValue (Pair reify x))
      (\(ApplyForeach x) -> toEnc (Pair reify x))
  toJSONKeyList = case toJSONKeyForeach of
    ToJSONKeyTextForall toText toEnc -> ToJSONKeyValue
      (\xs -> toJSON $ map (\(ApplyForeach x) -> toText (Pair reify x)) xs)
      (\xs -> Aeson.list (textEncodingToValueEncoding . toEnc . Pair reify) (map getApplyForeach xs))
    ToJSONKeyValueForall toValue toEnc -> ToJSONKeyValue
      (\xs -> toJSON $ map (\(ApplyForeach x) -> toValue (Pair reify x)) xs)
      (\xs -> Aeson.list (toEnc . Pair reify) (map getApplyForeach xs))

-- this is always safe
textEncodingToValueEncoding :: Aeson.Encoding' Text -> Aeson.Encoding' Aeson.Value
textEncodingToValueEncoding = AEI.retagEncoding

instance (FromJSONKeyForeach f, Reify a) => FromJSONKey (ApplyForeach f a) where
  fromJSONKey = case fromJSONKeyForeach of
    FromJSONKeyTextParserForeach f -> FromJSONKeyTextParser (fmap ApplyForeach . f reify)
    FromJSONKeyValueForeach f -> FromJSONKeyValue (fmap ApplyForeach . f reify)
  fromJSONKeyList = case fromJSONKeyForeach of
    FromJSONKeyTextParserForeach f -> FromJSONKeyValue $ Aeson.withArray "ApplyForeach" $ \xs -> do
      fmap V.toList (mapM (fmap ApplyForeach . Aeson.withText "ApplyForeach" (f reify)) xs)
    FromJSONKeyValueForeach f -> FromJSONKeyValue $ Aeson.withArray "ApplyForeach" $ \xs -> do
      fmap V.toList (mapM (fmap ApplyForeach . f reify) xs)

class EqForall f where
  eqForall :: f a -> f a -> Bool

-- | Variant of 'EqForall' that requires a pi-quantified type.
class EqForeach f where
  eqForeach :: Sing a -> f a -> f a -> Bool

class EqForall f => OrdForall f where
  compareForall :: f a -> f a -> Ordering

class EqForall f => EqForallPoly f where
  eqForallPoly :: f a -> f b -> WitnessedEquality a b
  default eqForallPoly :: TestEquality f => f a -> f b -> WitnessedEquality a b
  eqForallPoly = defaultEqForallPoly

-- the default method does not work if your data type is a newtype wrapper
-- over a function, but that should not really ever happen.
class (OrdForall f, EqForallPoly f) => OrdForallPoly f where
  compareForallPoly :: f a -> f b -> WitnessedOrdering a b

-- | Variant of 'OrdForall' that requires a pi-quantified type.
class EqForeach f => OrdForeach f where
  compareForeach :: Sing a -> f a -> f a -> Ordering

class ShowForall f where
  showsPrecForall :: Int -> f a -> ShowS

class ShowForeach f where
  showsPrecForeach :: Sing a -> Int -> f a -> ShowS

class ShowForall2 f where
  showsPrecForall2 :: Int -> f a b -> ShowS

class ShowForeach2 f where
  showsPrecForeach2 :: Sing a -> Sing b -> Int -> f a b -> ShowS

showsForall :: ShowForall f => f a -> ShowS
showsForall = showsPrecForall 0

showsForeach :: ShowForeach f => Sing a -> f a -> ShowS
showsForeach s = showsPrecForeach s 0

showForall :: ShowForall f => f a -> String
showForall x = showsForall x ""

showsForall2 :: ShowForall2 f => f a b -> ShowS
showsForall2 = showsPrecForall2 0

showForall2 :: ShowForall2 f => f a b -> String
showForall2 x = showsForall2 x ""

class ReadExists f where
  readPrecExists :: R.ReadPrec (Exists f)

class EqForall2 f where
  eqForall2 :: f a b -> f a b -> Bool

class EqForallPoly2 (f :: k -> j -> Type) where 
  eqForallPoly2 :: forall (a :: k) (b :: j) (c :: k) (d :: j). f a b -> f c d -> WitnessedEquality '(a,b) '(c,d)

class HashableForall f where
  hashWithSaltForall :: Int -> f a -> Int

class HashableForeach f where
  hashWithSaltForeach :: Sing a -> Int -> f a -> Int

class ToJSONKeyForall f where
  toJSONKeyForall :: ToJSONKeyFunctionForall f

class ToJSONKeyForeach f where
  toJSONKeyForeach :: ToJSONKeyFunctionForall (Product Sing f)

class FromJSONKeyExists f where
  fromJSONKeyExists :: FromJSONKeyFunction (Exists f)

class FromJSONKeyForeach f where
  fromJSONKeyForeach :: FromJSONKeyFunctionForeach f

class ToJSONForall f where
  toJSONForall :: f a -> Aeson.Value

class ToJSONForeach f where
  toJSONForeach :: Sing a -> f a -> Aeson.Value

class FromJSONForeach f where
  parseJSONForeach :: Sing a -> Aeson.Value -> Aeson.Parser (f a)

class FromJSONExists f where
  parseJSONExists :: Aeson.Value -> Aeson.Parser (Exists f)

class EnumForall f where
  toEnumForall :: Int -> f a
  fromEnumForall :: f a -> Int

class EnumExists f where
  toEnumExists :: Int -> Exists f
  fromEnumExists :: Exists f -> Int

class BoundedExists f where
  minBoundExists :: Exists f
  maxBoundExists :: Exists f

class PathPieceExists f where
  fromPathPieceForall :: Text -> Maybe (Exists f)
  toPathPieceForall :: Exists f -> Text

class SemigroupForeach f where
  appendForeach :: Sing a -> f a -> f a -> f a

class SemigroupForall f where
  appendForall :: f a -> f a -> f a

class StorableForeach (f :: k -> Type) where
  peekForeach :: Sing a -> Ptr (f a) -> IO (f a)
  pokeForeach :: Sing a -> Ptr (f a) -> f a -> IO ()
  sizeOfForeach :: forall (a :: k). Proxy f -> Sing a -> Int

-- | This is like 'StorableForall' except that the type constructor
-- must ignore its argument (for purposes of representation).
class StorableForall (f :: k -> Type) where
  peekForall :: Ptr (f a) -> IO (f a)
  pokeForall :: Ptr (f a) -> f a -> IO ()
  sizeOfForall :: Proxy f -> Int

-- | Be careful with this typeclass. It is more unsafe than 'Prim'.
-- With 'writeByteArray#' and 'readByteArray#', one can implement
-- @unsafeCoerce@.
class PrimForall (f :: k -> Type) where
  sizeOfForall# :: Proxy# f -> Int#
  alignmentForall# :: Proxy# f -> Int#
  indexByteArrayForall# :: ByteArray# -> Int# -> f a
  readByteArrayForall# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, f a #)
  writeByteArrayForall# :: MutableByteArray# s -> Int# -> f a -> State# s -> State# s
  setByteArrayForall# :: MutableByteArray# s -> Int# -> Int# -> f a -> State# s -> State# s
  indexOffAddrForall# :: Addr# -> Int# -> f a
  readOffAddrForall# :: Addr# -> Int# -> State# s -> (# State# s, f a #)
  writeOffAddrForall# :: Addr# -> Int# -> f a -> State# s -> State# s
  setOffAddrForall# :: Addr# -> Int# -> Int# -> f a -> State# s -> State# s

class BinaryForeach (f :: k -> Type) where
  putForeach :: Sing a -> f a -> Put
  getForeach :: Sing a -> Get (f a)

class BinaryExists (f :: k -> Type) where
  putExists :: Exists f -> Put
  getExists :: Get (Exists f)

class BinaryExists2 (f :: k -> j -> Type) where
  putExists2 :: Exists2 f -> Put
  getExists2 :: Get (Exists2 f)

--------------------
-- Instances Below
--------------------

instance EqForall Proxy where
  eqForall _ _ = True

instance OrdForall Proxy where
  compareForall _ _ = EQ

instance ShowForall Proxy where
  showsPrecForall = showsPrec

instance ReadExists Proxy where
  readPrecExists = fmap Exists R.readPrec 

instance SemigroupForall Proxy where
  appendForall _ _ = Proxy 

instance EqForall ((:~:) a) where
  eqForall Refl Refl = True

instance EqForall2 (:~:) where
  eqForall2 Refl Refl = True



instance Eq a => EqForall (Const a) where
  eqForall (Const x) (Const y) = x == y

instance Ord a => OrdForall (Const a) where
  compareForall (Const x) (Const y) = compare x y

instance Hashable a => HashableForall (Const a) where
  hashWithSaltForall s (Const a) = hashWithSalt s a


-- I need to get rid of the ToJSONForall and FromJSONForeach constraints
-- on these two instances.
instance (ToJSONKeyForall f, ToJSONForall f) => ToJSONKey (Exists f) where
  toJSONKey = case toJSONKeyForall of
    ToJSONKeyTextForall t e -> ToJSONKeyText (\(Exists a) -> t a) (\(Exists a) -> e a)
    ToJSONKeyValueForall v e -> ToJSONKeyValue (\x -> case x of Exists a -> v a) (\(Exists a) -> e a)

instance (FromJSONKeyExists f, FromJSONExists f) => FromJSONKey (Exists f) where
  fromJSONKey = fromJSONKeyExists

instance EqForallPoly f => Eq (Exists f) where
  Exists a == Exists b = weakenEquality (eqForallPoly a b)

instance EqForallPoly2 f => Eq (Exists2 f) where
  Exists2 a == Exists2 b = weakenEquality (eqForallPoly2 a b)

instance OrdForallPoly f => Ord (Exists f) where
  compare (Exists a) (Exists b) = weakenOrdering (compareForallPoly a b)

instance HashableForall f => Hashable (Exists f) where
  hashWithSalt s (Exists a) = hashWithSaltForall s a

instance ToJSONForall f => ToJSON (Exists f) where
  toJSON (Exists a) = toJSONForall a

instance FromJSONExists f => FromJSON (Exists f) where
  parseJSON v = parseJSONExists v

instance ShowForall f => Show (Exists f) where
  showsPrec p (Exists a) = showParen 
    (p >= 11) 
    (showString "Exists " . showsPrecForall 11 a)

instance ShowForall2 f => Show (Exists2 f) where
  showsPrec p (Exists2 a) = showParen 
    (p >= 11) 
    (showString "Exists " . showsPrecForall2 11 a)

instance ReadExists f => Read (Exists f) where
  readPrec = R.parens $ R.prec 10 $ do
    R.Ident "Exists" <- R.lexP
    R.step readPrecExists
    
instance EnumExists f => Enum (Exists f) where
  fromEnum = fromEnumExists
  toEnum = toEnumExists

instance BoundedExists f => Bounded (Exists f) where
  minBound = minBoundExists
  maxBound = maxBoundExists

instance BinaryExists f => Binary (Exists f) where
  get = getExists
  put = putExists

instance BinaryExists2 f => Binary (Exists2 f) where
  get = getExists2
  put = putExists2

instance PathPieceExists f => PP.PathPiece (Exists f) where
  toPathPiece = toPathPieceForall
  fromPathPiece = fromPathPieceForall

instance (EqForall f, EqForall g) => EqForall (Product f g) where
  eqForall (Pair f1 g1) (Pair f2 g2) = eqForall f1 f2 && eqForall g1 g2

instance (EqForallPoly f, EqForallPoly g) => EqForallPoly (Product f g) where
  eqForallPoly (Pair f1 g1) (Pair f2 g2) = case eqForallPoly f1 f2 of
    WitnessedEqualityEqual -> eqForallPoly g1 g2
    WitnessedEqualityUnequal -> WitnessedEqualityUnequal

instance (OrdForall f, OrdForall g) => OrdForall (Product f g) where
  compareForall (Pair f1 g1) (Pair f2 g2) = mappend (compareForall f1 f2) (compareForall g1 g2)

instance (OrdForallPoly f, OrdForallPoly g) => OrdForallPoly (Product f g) where
  compareForallPoly (Pair f1 g1) (Pair f2 g2) = case compareForallPoly f1 f2 of
    WitnessedOrderingLT -> WitnessedOrderingLT
    WitnessedOrderingGT -> WitnessedOrderingGT
    WitnessedOrderingEQ -> compareForallPoly g1 g2

instance (ShowForall f, ShowForall g) => ShowForall (Product f g) where
  showsPrecForall p (Pair f g) = showParen 
    (p >= 11) 
    (showString "Pair " . showsPrecForall 11 f . showChar ' ' . showsPrecForall 11 g)

instance (Aeson.ToJSON1 f, ToJSONForall g) => ToJSONForall (Compose f g) where
  toJSONForall (Compose x) = Aeson.liftToJSON toJSONForall (Aeson.toJSON . map toJSONForall) x

instance (Aeson.ToJSON1 f, ToJSONForeach g) => ToJSONForeach (Compose f g) where
  toJSONForeach s (Compose x) = Aeson.liftToJSON (toJSONForeach s) (Aeson.toJSON . map (toJSONForeach s)) x

instance (Aeson.FromJSON1 f, FromJSONForeach g) => FromJSONForeach (Compose f g) where
  parseJSONForeach s = fmap Compose . Aeson.liftParseJSON
    (parseJSONForeach s)
    (Aeson.withArray "Compose" (fmap V.toList . V.mapM (parseJSONForeach s)))

instance (Eq1 f, EqForall g) => EqForall (Compose f g) where
  eqForall (Compose x) (Compose y) = liftEq eqForall x y

instance (Eq1 f, EqForeach g) => EqForeach (Compose f g) where
  eqForeach s (Compose x) (Compose y) = liftEq (eqForeach s) x y

instance (Show1 f, ShowForall g) => ShowForall (Compose f g) where
  showsPrecForall p (Compose x) = showParen (p > 10) $ showString "Compose " . liftShowsPrec showsPrecForall showListForall 11 x

instance (Show1 f, ShowForeach g) => ShowForeach (Compose f g) where
  showsPrecForeach s p (Compose x) = showParen (p > 10) $ showString "Compose " . liftShowsPrec (showsPrecForeach s) (showListForeach s) 11 x

instance (Semigroup1 f, SemigroupForeach g) => SemigroupForeach (Compose f g) where
  appendForeach s (Compose x) (Compose y) = Compose (liftAppend (appendForeach s) x y)

instance (Binary1 f, BinaryForeach g) => BinaryForeach (Compose f g) where
  putForeach s (Compose x) = liftPut (putForeach s) x
  getForeach s = fmap Compose (liftGet (getForeach s))

showListForall :: ShowForall f => [f a] -> ShowS
showListForall = showList__ showsForall

showListForeach :: ShowForeach f => Sing a -> [f a] -> ShowS
showListForeach s = showList__ (showsForeach s)

-- Copied from GHC.Show. I do not like to import internal modules
-- if I can instead copy a small amount of code.
showList__ :: (a -> ShowS) ->  [a] -> ShowS
showList__ _     []     s = "[]" ++ s
showList__ showx (x:xs) s = '[' : showx x (showl xs)
  where
    showl []     = ']' : s
    showl (y:ys) = ',' : showx y (showl ys)

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

defaultEqForallPoly :: (TestEquality f, EqForall f) => f a -> f b -> WitnessedEquality a b
defaultEqForallPoly x y = case testEquality x y of
  Nothing -> WitnessedEqualityUnequal
  Just Refl -> if eqForall x y then WitnessedEqualityEqual else WitnessedEqualityUnequal

getTagBox :: a -> Int
getTagBox !x = I# (dataToTag# x)
{-# INLINE getTagBox #-}

type family Sing = (r :: k -> Type) | r -> k

-- | The two functions must form an isomorphism.
class SingKind k where
  demoteSing :: Sing (a :: k) -> k
  promoteSing :: k -> Exists (Sing :: k -> Type)

instance SingKind k => SingKind [k] where
  demoteSing SingListNil = []
  demoteSing (SingListCons s ss) = demoteSing s : demoteSing ss
  promoteSing [] = Exists SingListNil
  promoteSing (x : xs) = case promoteSing x of
    Exists s -> case promoteSing xs of
      Exists ss -> Exists (SingListCons s ss)

type instance Sing = SingList
type instance Sing = SingMaybe

class Unreify k where
  unreify :: forall (a :: k) b. Sing a -> (Reify a => b) -> b

instance Unreify k => Unreify [k] where
  unreify = unreifyList

class Reify a where
  reify :: Sing a

instance Reify '[] where
  reify = SingListNil

instance (Reify a, Reify as) => Reify (a ': as) where
  reify = SingListCons reify reify

instance Reify 'Nothing where
  reify = SingMaybeNothing

instance Reify a => Reify ('Just a) where
  reify = SingMaybeJust reify

class EqSing k where
  eqSing :: forall (a :: k) (b :: k). Sing a -> Sing b -> Maybe (a :~: b)

class EqSing k => OrdSing k where
  compareSing :: forall (a :: k) (b :: k). Sing a -> Sing b -> WitnessedOrdering a b

class ShowSing k where
  showsPrecSing :: forall (a :: k). Int -> Sing a -> ShowS

instance EqSing a => EqSing [a] where
  eqSing = eqSingList

eqSingList :: forall (a :: [k]) (b :: [k]). EqSing k => SingList a -> SingList b -> Maybe (a :~: b)
eqSingList SingListNil SingListNil = Just Refl
eqSingList SingListNil (SingListCons _ _) = Nothing
eqSingList (SingListCons _ _) SingListNil = Nothing
eqSingList (SingListCons a as) (SingListCons b bs) = case eqSing a b of
  Just Refl -> case eqSingList as bs of
    Just Refl -> Just Refl
    Nothing -> Nothing
  Nothing -> Nothing

class SemigroupForeach f => MonoidForeach f where
  emptyForeach :: Sing a -> f a

class SemigroupForall f => MonoidForall f where
  emptyForall :: f a

data SingList :: forall (k :: Type). [k] -> Type where
  SingListNil :: SingList '[]
  SingListCons :: Sing r -> SingList rs -> SingList (r ': rs)

-- singletons can only have one inhabitant per type, so if the
-- types are equal, the values must be equal
instance EqForall SingList where
  eqForall _ _ = True

instance EqSing k => EqForallPoly (SingList :: [k] -> Type) where
  eqForallPoly SingListNil SingListNil = WitnessedEqualityEqual
  eqForallPoly SingListNil (SingListCons _ _) = WitnessedEqualityUnequal
  eqForallPoly (SingListCons _ _) SingListNil = WitnessedEqualityUnequal
  eqForallPoly (SingListCons r rs) (SingListCons s ss) = case eqSing r s of
    Nothing -> WitnessedEqualityUnequal
    Just Refl -> case eqForallPoly rs ss of
      WitnessedEqualityUnequal -> WitnessedEqualityUnequal
      WitnessedEqualityEqual -> WitnessedEqualityEqual

instance (SingKind k, Binary k) => BinaryExists (SingList :: [k] -> Type) where
  putExists (Exists xs) = BN.put (demoteSing xs)
  getExists = fmap promoteSing BN.get

instance (ShowSing k) => Show (SingList (xs :: [k])) where
  showsPrec _ SingListNil = showString "SingListNil"
  showsPrec p (SingListCons s ss) = showParen (p > 10)
    $ showString "SingListCons "
    . showsPrecSing 11 s
    . showChar ' '
    . showsPrec 11 ss

instance ShowSing k => ShowSing [k] where
  showsPrecSing = showsPrec

data SingMaybe :: Maybe k -> Type where
  SingMaybeJust :: Sing a -> SingMaybe ('Just a)
  SingMaybeNothing :: SingMaybe 'Nothing

unreifyList :: forall (as :: [k]) b. Unreify k
  => SingList as
  -> (Reify as => b)
  -> b
unreifyList SingListNil b = b
unreifyList (SingListCons s ss) b = unreify s (unreifyList ss b)

instance (EqForeach f, EqSing k) => Eq (Some (f :: k -> Type)) where 
  Some s1 v1 == Some s2 v2 = case eqSing s1 s2 of
    Just Refl -> eqForeach s1 v1 v2
    Nothing -> False

instance (OrdForeach f, OrdSing k) => Ord (Some (f :: k -> Type)) where 
  compare (Some s1 v1) (Some s2 v2) = case compareSing s1 s2 of
    WitnessedOrderingEQ -> compareForeach s1 v1 v2
    WitnessedOrderingLT -> LT
    WitnessedOrderingGT -> GT

instance (ShowForeach f, ShowSing k) => Show (Some (f :: k -> Type)) where
  showsPrec p (Some s a) = showParen (p >= 11)
    $ showString "Sing "
    . showsPrecSing 11 s
    . showChar ' '
    . showsPrecForeach s 11 a

class ToSing (f :: k -> Type) where
  toSing :: f a -> Sing a

class ToJSONSing k where
  toJSONSing :: forall (a :: k). Sing a -> Aeson.Value

instance (ToJSONForeach f, ToJSONSing k) => ToJSON (Some (f :: k -> Type)) where
  toJSON (Some s v) = toJSON [toJSONSing s, toJSONForeach s v]

class FromJSONSing k where
  parseJSONSing :: Aeson.Value -> Aeson.Parser (Exists (Sing :: k -> Type))

instance (FromJSONForeach f, FromJSONSing k) => FromJSON (Some (f :: k -> Type)) where
  parseJSON = Aeson.withArray "Some" $ \v -> if V.length v == 2
    then do
      let x = V.unsafeIndex v 0
          y = V.unsafeIndex v 1
      Exists s <- parseJSONSing x :: Aeson.Parser (Exists (Sing :: k -> Type))
      val <- parseJSONForeach s y
      return (Some s val)
    else fail "array of length 2 expected"

-- This name is not great. I need to figure out a better naming
-- scheme that allows this area to grow.
toJSONMapForeachKey :: (ToJSONKeyForeach f, ToJSONForeach v)
  => Sing a
  -> Map (f a) (v a)
  -> Aeson.Value
toJSONMapForeachKey s m = case toJSONKeyForeach of
  ToJSONKeyTextForall keyToText _ -> toJSON $ M.foldlWithKey'
    ( \hm key val -> HM.insert (keyToText (Pair s key)) (toJSONForeach s val) hm
    ) HM.empty m
  ToJSONKeyValueForall keyToValue _ -> toJSON $ M.foldrWithKey' 
    ( \key val xs -> (keyToValue (Pair s key), toJSONForeach s val) : xs
    ) [] m

-- | Parse a 'Map' whose key type is higher-kinded. This only creates a valid 'Map'
--   if the 'OrdForeach' instance agrees with the 'Ord' instance.
parseJSONMapForeachKey :: forall k (f :: k -> Type) (a :: k) v. (FromJSONKeyForeach f, OrdForeach f, Unreify k)
  => (Aeson.Value -> Aeson.Parser v) 
  -> Sing a
  -> Aeson.Value
  -> Aeson.Parser (Map (f a) v)
parseJSONMapForeachKey valueParser s obj = unreify s $ case fromJSONKeyForeach of
  FromJSONKeyTextParserForeach f -> Aeson.withObject "Map k v"
    ( fmap (M.mapKeysMonotonic getApplyForeach) . HM.foldrWithKey
      (\k v m -> M.insert
        <$> (coerce (f s k :: Aeson.Parser (f a)) :: Aeson.Parser (ApplyForeach f a)) <?> Key k
        <*> valueParser v <?> Key k
        <*> m
      ) (pure M.empty)
    ) obj
  FromJSONKeyValueForeach f -> Aeson.withArray "Map k v"
    ( fmap (M.mapKeysMonotonic getApplyForeach . M.fromList)
    . (coerce :: Aeson.Parser [(f a, v)] -> Aeson.Parser [(ApplyForeach f a, v)])
    . TRV.sequence
    . zipWith (parseIndexedJSONPair (f s) valueParser) [0..]
    . V.toList
    ) obj

-- copied from aeson
parseIndexedJSONPair :: (Aeson.Value -> Aeson.Parser a) -> (Aeson.Value -> Aeson.Parser b) -> Int -> Aeson.Value -> Aeson.Parser (a, b)
parseIndexedJSONPair keyParser valParser idx value = p value <?> Index idx
  where
    p = Aeson.withArray "(k,v)" $ \ab ->
        let n = V.length ab
        in if n == 2
             then (,) <$> parseJSONElemAtIndex keyParser 0 ab
                      <*> parseJSONElemAtIndex valParser 1 ab
             else fail $ "cannot unpack array of length " ++
                         show n ++ " into a pair"
{-# INLINE parseIndexedJSONPair #-}

-- copied from aeson
parseJSONElemAtIndex :: (Aeson.Value -> Aeson.Parser a) -> Int -> V.Vector Aeson.Value -> Aeson.Parser a
parseJSONElemAtIndex p idx ary = p (V.unsafeIndex ary idx) <?> Index idx

weakenEquality :: WitnessedEquality a b -> Bool
weakenEquality = \case
  WitnessedEqualityEqual -> True
  WitnessedEqualityUnequal -> False

weakenOrdering :: WitnessedOrdering a b -> Ordering
weakenOrdering = \case
  WitnessedOrderingGT -> GT
  WitnessedOrderingEQ -> EQ
  WitnessedOrderingLT -> LT

strengthenEquality :: Bool -> WitnessedEquality a a
strengthenEquality = \case
  True -> WitnessedEqualityEqual
  False -> WitnessedEqualityUnequal

-- | Given that we already know two types are equal, promote an 'Ordering'.
strengthenOrdering :: Ordering -> WitnessedOrdering a a                                
strengthenOrdering = \case
  LT -> WitnessedOrderingLT                                                    
  EQ -> WitnessedOrderingEQ                                                              
  GT -> WitnessedOrderingGT                                                                

-- | Given that we already know two types to be unequal, promote an 'Ordering'.
-- The argument should not be @EQ@.
strengthenUnequalOrdering :: Ordering -> WitnessedOrdering a b                   
strengthenUnequalOrdering = \case                                                  
  LT -> WitnessedOrderingLT 
  EQ -> WitnessedOrderingLT -- this case should not happen                                          
  GT -> WitnessedOrderingGT               

instance (EqForallPoly f, ToSing f, EqForeach g) => Eq (DependentPair f g) where
  DependentPair a1 b1 == DependentPair a2 b2 = case eqForallPoly a1 a2 of
    WitnessedEqualityUnequal -> False
    WitnessedEqualityEqual -> eqForeach (toSing a1) b1 b2

instance (OrdForallPoly f, ToSing f, OrdForeach g) => Ord (DependentPair f g) where
  compare (DependentPair a1 b1) (DependentPair a2 b2) = case compareForallPoly a1 a2 of
    WitnessedOrderingLT -> LT
    WitnessedOrderingGT -> GT
    WitnessedOrderingEQ -> compareForeach (toSing a1) b1 b2

instance (ShowForall f, ToSing f, ShowForeach g) => Show (DependentPair f g) where
  showsPrec p (DependentPair a b) s = showParen 
    (p >= 11) 
    (showString "DependentPair " . showsPrecForall 11 a . showChar ' ' . showsPrecForeach (toSing a) 11 b)
    s


