{-# LANGUAGE BangPatterns, UnboxedTuples, Safe #-}
module Data.RangeSet.Internal.Lumpers (module Data.RangeSet.Internal.Lumpers) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.SmartConstructors
import Data.RangeSet.Internal.Inserters
import Data.RangeSet.Internal.Extractors
import Data.RangeSet.Internal.Enum

{-# INLINABLE link #-}
link :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
link !l !u Tip Tip = single (diffE l u) l u
link l u Tip (Fork rh rsz rl ru rlt rrt) = insertLAdj (diffE l u) l u rh rsz rl ru rlt rrt
link l u (Fork lh lsz ll lu llt lrt) Tip = insertRAdj (diffE l u) l u lh lsz ll lu llt lrt
link l u lt@(Fork _ lsz ll lu llt lrt) rt@(Fork _ rsz rl ru rlt rrt) =
  disjointLink (diffE l' u') l' u' lt'' rt''
  where
    -- we have to check for fusion up front
    (# !lmaxl, !lmaxu, lt' #) = maxDelete lsz ll lu llt lrt
    (# !rminl, !rminu, rt' #) = minDelete rsz rl ru rlt rrt

    (# !l', !lt'' #) | lmaxu == pred l = (# lmaxl, lt' #)
                     | otherwise       = (# l, lt #)

    (# !u', !rt'' #) | rminl == succ u = (# rminu, rt' #)
                     | otherwise       = (# u, rt #)

{-# INLINEABLE disjointLink #-}
disjointLink :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
disjointLink !newSz !l !u Tip rt = unsafeInsertL newSz l u rt
disjointLink newSz l u lt Tip = unsafeInsertR newSz l u lt
disjointLink newSz l u lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (newSz + szl + szr) rl ru (disjointLink newSz l u lt rlt) rrt
  | hr < hl + 1 = balanceR (newSz + szl + szr) ll lu llt (disjointLink newSz l u lrt rt)
  | otherwise   = forkH (newSz + szl + szr) l u hl lt hr rt

-- This version checks for fusion between the two trees to be merged
{-{-# INLINEABLE merge #-}
merge :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
merge Tip Tip = Tip
merge t Tip = t
merge Tip t = t
merge t1 t2 =
  let (# !_, !u1 #) = unsafeMaxRange t1
      (# !l2, !u2, t2' #) = unsafeMinDelete t2
  in if succ u1 == l2 then unsafeMerge (unsafeFuseR (diffE l2 u2) u2 t1) t2'
     else unsafeMerge t1 t2-}

-- This assumes that the trees are /totally/ disjoint
{-# INLINEABLE disjointMerge #-}
disjointMerge :: RangeSet a -> RangeSet a -> RangeSet a
disjointMerge Tip rt = rt
disjointMerge lt Tip = lt
disjointMerge lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (szl + szr) rl ru (disjointMerge lt rlt) rrt
  | hr < hl + 1 = balanceR (szl + szr) ll lu llt (disjointMerge lrt rt)
  | otherwise   = glue (szl + szr) lt rt

-- Trees must be balanced with respect to eachother, since we pull from the tallest, no balancing is required
{-# INLINEABLE glue #-}
glue :: Size -> RangeSet a -> RangeSet a -> RangeSet a
glue !_ Tip rt = rt
glue _ lt Tip  = lt
glue sz lt@(Fork lh lsz ll lu llt lrt) rt@(Fork rh rsz rl ru rlt rrt)
  | lh < rh = let (# !l, !u, !rt' #) = minDelete rsz rl ru rlt rrt in forkSz sz l u lt rt'
  | otherwise = let (# !l, !u, !lt' #) = maxDelete lsz ll lu llt lrt in forkSz sz l u lt' rt

