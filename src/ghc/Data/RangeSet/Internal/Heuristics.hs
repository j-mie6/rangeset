{-# LANGUAGE BangPatterns, MagicHash, CPP #-}
#ifdef SAFE
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Unsafe #-}
#endif
module Data.RangeSet.Internal.Heuristics (stayedSame, ifStayedSame) where

import Prelude

#ifndef SAFE
import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)
#endif

import Data.RangeSet.Internal.Types

#ifndef SAFE
{-# INLINE ptrEq #-}
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)
#endif

{-# INLINE stayedSame #-}
{-|
This should /only/ be used to compare a set that is modified
with its original value. The assumption is that a set as stayed
the same if its size hasn't changed.
-}
stayedSame :: RangeSet a -- ^ the original set
           -> RangeSet a -- ^ the same (?) set post modification
           -> Bool
stayedSame before after =
#ifdef SAFE
    size before == size after
#else
    before `ptrEq` after
#endif

{-# INLINE ifStayedSame #-}
ifStayedSame :: RangeSet a -> RangeSet a -> RangeSet a -> (RangeSet a -> RangeSet a) -> RangeSet a
ifStayedSame !x !x' y f = if size x == size x' then y else f x'
