{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Exists.Aeson
  ( FromJSONForall(..)
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
  , ToJSONSing(..)
  , FromJSONSing(..)
  , parseJSONMapForeachKey
  , toJSONMapForeachKey
  ) where

import Control.Applicative (Const(..))
import Data.Aeson ((<?>))
import Data.Aeson (ToJSON(..),FromJSON(..))
import Data.Aeson (ToJSONKey(..),FromJSONKey(..))
import Data.Aeson (ToJSONKeyFunction(..),FromJSONKeyFunction(..))
import Data.Aeson.Types (JSONPathElement(Key,Index))
import Data.Coerce (coerce)
import Data.Exists (Exists(..),Some(..),Sing,ApplyForeach(..),OrdForeach)
import Data.Exists (Reify(..),Unreify(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Product (Product(..))
import Data.Kind (Type)
import Data.Map.Strict (Map)

import qualified Data.Aeson.Encoding as Aeson
import qualified Data.Aeson.Encoding.Internal as AEI
import qualified Data.Aeson.Key as Key
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Aeson.Types as Aeson
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.Traversable as TRV
import qualified Data.Vector as V

data ToJSONKeyFunctionForall f
  = ToJSONKeyTextForall !(forall a. f a -> Aeson.Key) !(forall a. f a -> Aeson.Encoding' Aeson.Key)
  | ToJSONKeyValueForall !(forall a. f a -> Aeson.Value) !(forall a. f a -> Aeson.Encoding)
data FromJSONKeyFunctionForeach f
  = FromJSONKeyTextParserForeach !(forall a. Sing a -> Aeson.Key -> Aeson.Parser (f a))
  | FromJSONKeyValueForeach !(forall a. Sing a -> Aeson.Value -> Aeson.Parser (f a))

instance (ToJSONForeach f, Reify a) => ToJSON (ApplyForeach f a) where
  toJSON = toJSONForeach reify

instance (FromJSONForeach f, Reify a) => FromJSON (ApplyForeach f a) where
  parseJSON = parseJSONForeach reify

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
textEncodingToValueEncoding :: Aeson.Encoding' Aeson.Key -> Aeson.Encoding' Aeson.Value
textEncodingToValueEncoding = AEI.retagEncoding

instance (FromJSONKeyForeach f, Reify a) => FromJSONKey (ApplyForeach f a) where
  fromJSONKey = case fromJSONKeyForeach of
    FromJSONKeyTextParserForeach f -> FromJSONKeyTextParser (fmap ApplyForeach . f reify . Key.fromText)
    FromJSONKeyValueForeach f -> FromJSONKeyValue (fmap ApplyForeach . f reify)
  fromJSONKeyList = case fromJSONKeyForeach of
    FromJSONKeyTextParserForeach f -> FromJSONKeyValue $ Aeson.withArray "ApplyForeach" $ \xs -> do
      fmap V.toList (mapM (fmap ApplyForeach . Aeson.withText "ApplyForeach" (f reify . Key.fromText)) xs)
    FromJSONKeyValueForeach f -> FromJSONKeyValue $ Aeson.withArray "ApplyForeach" $ \xs -> do
      fmap V.toList (mapM (fmap ApplyForeach . f reify) xs)

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

class FromJSONForall f where
  parseJSONForall :: Sing a -> Aeson.Value -> Aeson.Parser (f a)

class FromJSONForeach f where
  parseJSONForeach :: Sing a -> Aeson.Value -> Aeson.Parser (f a)

class FromJSONExists f where
  parseJSONExists :: Aeson.Value -> Aeson.Parser (Exists f)

instance FromJSON a => FromJSONForeach (Const a) where
  parseJSONForeach _ = fmap Const . parseJSON

instance ToJSON a => ToJSONForeach (Const a) where
  toJSONForeach _ = coerce (toJSON @a)

-- I need to get rid of the ToJSONForall and FromJSONForeach constraints
-- on these two instances.
instance (ToJSONKeyForall f, ToJSONForall f) => ToJSONKey (Exists f) where
  toJSONKey = case toJSONKeyForall of
    ToJSONKeyTextForall t e -> ToJSONKeyText (\(Exists a) -> t a) (\(Exists a) -> e a)
    ToJSONKeyValueForall v e -> ToJSONKeyValue (\x -> case x of Exists a -> v a) (\(Exists a) -> e a)

instance (FromJSONKeyExists f, FromJSONExists f) => FromJSONKey (Exists f) where
  fromJSONKey = fromJSONKeyExists

instance ToJSONForall f => ToJSON (Exists f) where
  toJSON (Exists a) = toJSONForall a

instance FromJSONExists f => FromJSON (Exists f) where
  parseJSON v = parseJSONExists v

instance (Aeson.ToJSON1 f, ToJSONForall g) => ToJSONForall (Compose f g) where
  toJSONForall (Compose x) = Aeson.liftToJSON (\_ -> False) toJSONForall (Aeson.toJSON . map toJSONForall) x

instance (Aeson.ToJSON1 f, ToJSONForeach g) => ToJSONForeach (Compose f g) where
  toJSONForeach s (Compose x) = Aeson.liftToJSON (\_ -> False) (toJSONForeach s) (Aeson.toJSON . map (toJSONForeach s)) x

instance (Aeson.FromJSON1 f, FromJSONForeach g) => FromJSONForeach (Compose f g) where
  parseJSONForeach s = fmap Compose . Aeson.liftParseJSON Nothing
    (parseJSONForeach s)
    (Aeson.withArray "Compose" (fmap V.toList . V.mapM (parseJSONForeach s)))

class ToJSONSing k where
  toJSONSing :: forall (a :: k). Sing a -> Aeson.Value

instance (ToJSONForeach f, ToJSONSing k) => ToJSON (Some (f :: k -> Type)) where
  toJSON (Some s v) = toJSON [toJSONSing s, toJSONForeach s v]

class FromJSONSing k where
  parseJSONSing :: Aeson.Value -> Aeson.Parser (Exists (Sing :: k -> Type))

instance (Aeson.FromJSON1 f, FromJSONForall g) => FromJSONForall (Compose f g) where
  parseJSONForall s = fmap Compose . Aeson.liftParseJSON Nothing
      (parseJSONForall s)
          (Aeson.withArray "Compose" (fmap V.toList . V.mapM (parseJSONForall s)))

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
    ( fmap (M.mapKeysMonotonic getApplyForeach) . KM.foldrWithKey
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
