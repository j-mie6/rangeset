{-# LANGUAGE BangPatterns, UnboxedTuples #-}
module Data.RangeSet.Internal.Inserters (module Data.RangeSet.Internal.Inserters) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.SmartConstructors
import Data.RangeSet.Internal.Extractors

{-|
Inserts an range at the left-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertL #-}
unsafeInsertL :: Size -> E -> E -> RangeSet a -> RangeSet a
unsafeInsertL !newSz !l !u = go
  where
    go :: RangeSet a -> RangeSet a
    go Tip = single newSz l u
    go (Fork _ sz l' u' lt rt) = balanceL (sz + newSz) l' u' (go lt) rt

{-|
Inserts an range at the right-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertR #-}
unsafeInsertR :: Size -> E -> E -> RangeSet a -> RangeSet a
unsafeInsertR !newSz !l !u = go
  where
    go :: RangeSet a -> RangeSet a
    go Tip = single newSz l u
    go (Fork _ sz l' u' lt rt) = balanceR (sz + newSz) l' u' lt (go rt)

{-# INLINEABLE insertLAdj #-}
insertLAdj :: Size -> E -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertLAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case minRange tl tu tlt of
  (# !l', _ #) | l' == succ u -> fuseL newSz l th tsz tl tu tlt trt
               | otherwise    -> balanceL (tsz + newSz) tl tu (unsafeInsertL newSz l u tlt) trt
  where
    {-# INLINEABLE fuseL #-}
    fuseL :: Size -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseL !newSz !l' !h !sz !l !u lt rt = case lt of
      Tip -> Fork h (newSz + sz) l' u Tip rt
      Fork lh lsz ll lu llt lrt  -> Fork h (newSz + sz) l u (fuseL newSz l' lh lsz ll lu llt lrt) rt

{-# INLINEABLE insertRAdj #-}
insertRAdj :: Size -> E -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertRAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case maxRange tl tu trt of
  (# _, !u' #) | u' == pred l -> fuseR newSz u th tsz tl tu tlt trt
               | otherwise    -> balanceR (tsz + newSz) tl tu tlt (unsafeInsertR newSz l u trt)
  where
    {-# INLINEABLE fuseR #-}
    fuseR :: Size -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseR !newSz !u' !h !sz !l !u lt rt = case rt of
      Tip -> Fork h (newSz + sz) l u' lt Tip
      Fork rh rsz rl ru rlt rrt  -> Fork h (newSz + sz) l u lt (fuseR newSz u' rh rsz rl ru rlt rrt)
