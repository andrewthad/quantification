{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Binary.Lifted
  ( Binary1(..)
  , put1
  , get1
  ) where

import Data.Binary (Get,Put,Binary,get,put)
import Data.Functor.Compose (Compose(..))
import Data.Word (Word8)

class Binary1 f where
  liftPut :: (a -> Put) -> f a -> Put
  liftGet :: Get a -> Get (f a)

instance Binary1 [] where
  liftPut = liftPutList
  liftGet = liftGetList

instance Binary1 Maybe where
  liftPut _ Nothing  = put (0 :: Word8)
  liftPut f (Just x) = put (1 :: Word8) <> f x
  liftGet f = do
    (w :: Word8) <- get
    case w of
      0 -> return Nothing
      _ -> fmap Just f

instance (Binary1 f, Binary1 g) => Binary1 (Compose f g) where
  liftPut f (Compose x) = liftPut (liftPut f) x
  liftGet f = fmap Compose (liftGet (liftGet f))

liftPutList :: (a -> Put) -> [a] -> Put
liftPutList f xs = put (length xs) <> mapM_ f xs                                

liftGetList :: Get a -> Get [a]                                                    
liftGetList g = do
  n <- get :: Get Int                                                           
  internalGetMany g n                                                              

internalGetMany :: Get a -> Int -> Get [a]                                         
internalGetMany g n = go [] n                                                      
  where 
  go xs !0 = return $! reverse xs                                                  
  go xs !i = do                                                                    
    !x <- g
    go (x:xs) (i-1)                                                                

get1 :: (Binary1 f, Binary a) => Get (f a)
get1 = liftGet get

put1 :: (Binary1 f, Binary a) => f a -> Put
put1 = liftPut put


