{-# LANGUAGE BangPatterns, MagicHash, Unsafe #-}
module Data.RangeSet.Internal.Unsafe (ptrEq) where

import Prelude
import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)

{-# INLINE ptrEq #-}
ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
