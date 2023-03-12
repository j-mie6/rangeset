{-# LANGUAGE BangPatterns, UnboxedTuples, Safe #-}
module Data.RangeSet.Internal.Lumpers (module Data.RangeSet.Internal.Lumpers) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.SmartConstructors
import Data.RangeSet.Internal.Inserters
import Data.RangeSet.Internal.Extractors

{-# INLINABLE link #-}
link :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
link !l !u Tip Tip = single l u
link l u Tip (Fork rh rl ru rlt rrt) = insertLAdj l u rh rl ru rlt rrt
link l u (Fork lh ll lu llt lrt) Tip = insertRAdj l u lh ll lu llt lrt
link l u lt@(Fork _ ll lu llt lrt) rt@(Fork _ rl ru rlt rrt) =
  disjointLink l' u' lt'' rt''
  where
    -- we have to check for fusion up front
    (# !lmaxl, !lmaxu, lt' #) = maxDelete ll lu llt lrt
    (# !rminl, !rminu, rt' #) = minDelete rl ru rlt rrt

    (# !l', !lt'' #) | lmaxu == pred l = (# lmaxl, lt' #)
                     | otherwise       = (# l, lt #)

    (# !u', !rt'' #) | rminl == succ u = (# rminu, rt' #)
                     | otherwise       = (# u, rt #)

{-# INLINEABLE disjointLink #-}
disjointLink :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
disjointLink !l !u Tip rt = unsafeInsertL l u rt
disjointLink l u lt Tip = unsafeInsertR l u lt
disjointLink l u lt@(Fork hl ll lu llt lrt) rt@(Fork hr rl ru rlt rrt)
  | hl < hr + 1 = balanceL rl ru (disjointLink l u lt rlt) rrt
  | hr < hl + 1 = balanceR ll lu llt (disjointLink l u lrt rt)
  | otherwise   = forkH l u hl lt hr rt

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
disjointMerge lt@(Fork hl ll lu llt lrt) rt@(Fork hr rl ru rlt rrt)
  | hl < hr + 1 = balanceL rl ru (disjointMerge lt rlt) rrt
  | hr < hl + 1 = balanceR ll lu llt (disjointMerge lrt rt)
  | otherwise   = glue lt rt

-- Trees must be balanced with respect to eachother, since we pull from the tallest, no balancing is required
{-# INLINEABLE glue #-}
glue :: RangeSet a -> RangeSet a -> RangeSet a
glue Tip rt = rt
glue lt Tip  = lt
glue lt@(Fork lh ll lu llt lrt) rt@(Fork rh rl ru rlt rrt)
  | lh < rh = let (# !l, !u, !rt' #) = minDelete rl ru rlt rrt in fork l u lt rt'
  | otherwise = let (# !l, !u, !lt' #) = maxDelete ll lu llt lrt in fork l u lt' rt
