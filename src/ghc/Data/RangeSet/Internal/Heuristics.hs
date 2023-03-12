{-# LANGUAGE BangPatterns, Unsafe #-}
module Data.RangeSet.Internal.Heuristics (stayedSame, ifStayedSame) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.Unsafe

{-# INLINE stayedSame #-}
{-|
This should /only/ be used to compare a set that is modified
with its original value. The assumption is that a set as stayed
the same if its size hasn't changed.
-}
stayedSame :: RangeSet a -- ^ the original set
           -> RangeSet a -- ^ the same (?) set post modification
           -> Bool
stayedSame !before !after = before `ptrEq` after

{-# INLINE ifStayedSame #-}
ifStayedSame :: RangeSet a -> RangeSet a -> RangeSet a -> (RangeSet a -> RangeSet a) -> RangeSet a
ifStayedSame !x !x' y f = if x `ptrEq` x' then y else f x'
