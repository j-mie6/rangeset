{-# LANGUAGE BangPatterns #-}
module Data.RangeSet.Internal.Enum (module Data.RangeSet.Internal.Enum) where

import Prelude

import Data.RangeSet.Internal.Types (E, Size)

{-# INLINE range #-}
range :: Enum a => a -> a -> [a]
range l u = [l..u]

{-# INLINE diffE #-}
diffE :: E -> E -> Size
diffE !l !u = u - l + 1
