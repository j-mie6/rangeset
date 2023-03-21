{-# LANGUAGE UnboxedTuples, BangPatterns, Safe #-}
module Data.RangeSet.SetCrossSet (union, intersection, difference, disjoint) where

import Prelude
import Data.RangeSet.Internal

{-|
Unions two sets together such that if and only if an element appears in either one of the sets, it
will appear in the result set.

@since 0.0.1.0
-}
union :: RangeSet a -> RangeSet a -> RangeSet a
union = optimalForHeight
  where
    optimalForHeight :: RangeSet a -> RangeSet a -> RangeSet a
    optimalForHeight t Tip =  t
    optimalForHeight Tip t = t
    optimalForHeight lt@(Fork lh ll lu llt lrt) rt@(Fork rh rl ru rlt rrt)
      | lh < rh = doUnion rt rl ru rlt rrt ll lu llt lrt
      | otherwise = doUnion lt ll lu llt lrt rl ru rlt rrt

    doUnion :: RangeSet a -> E -> E -> RangeSet a -> RangeSet a -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    doUnion t ll lu llt lrt rl ru rlt rrt = case splitFork ll lu rl ru rlt rrt of
      (# lt', rt' #)
        | stayedSame llt ltlt', stayedSame lrt rtrt' -> t
        | otherwise                                  -> link ll lu ltlt' rtrt'
        where !ltlt' = llt `optimalForHeight` lt'
              !rtrt' = lrt `optimalForHeight` rt'

{-|
Intersects two sets such that an element appears in the result if and only if it is present in both
of the provided sets.

@since 0.0.1.0
-}
intersection :: RangeSet a -> RangeSet a -> RangeSet a
intersection = optimalForHeight
  where
    -- until splitOverlapFork is optimised, this picks the best configuration for performance
    -- this is because more work is done on the right tree than the left tree, so making the
    -- right tree the shallowest saves work in long run
    optimalForHeight :: RangeSet a -> RangeSet a -> RangeSet a
    optimalForHeight Tip _ = Tip
    optimalForHeight _ Tip = Tip
    optimalForHeight lt@(Fork lh ll lu llt lrt) rt@(Fork rh rl ru rlt rrt)
      | lh < rh = doIntersect rt rl ru rlt rrt ll lu llt lrt
      | otherwise = doIntersect lt ll lu llt lrt rl ru rlt rrt

    doIntersect :: RangeSet a -> E -> E -> RangeSet a -> RangeSet a -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    doIntersect !lt !ll !lu !llt !lrt !rl !ru !rlt !rrt =
      case overlap of
        Tip -> disjointMerge lltrlt lrtrrt
        Fork 1 x y _ _
          | x == ll, y == lu
          , stayedSame llt lltrlt, stayedSame lrt lrtrrt -> lt
          | otherwise -> disjointLink x y lltrlt lrtrrt
        Fork _ x y lt' rt' -> disjointLink x y (disjointMerge lltrlt lt') (disjointMerge rt' lrtrrt)
      where
        (# !lt', !overlap, !rt' #) = splitOverlapFork ll lu rl ru rlt rrt
        !lltrlt = optimalForHeight llt lt'
        !lrtrrt = optimalForHeight lrt rt'

{-|
Do two sets have no elements in common?

@since 0.0.1.0
-}
disjoint :: RangeSet a -> RangeSet a -> Bool
disjoint Tip _ = True
disjoint _ Tip = True
disjoint (Fork _ ll lu llt lrt) (Fork _ rl ru rlt rrt) = case splitOverlapFork ll lu rl ru rlt rrt of
  (# lt', Tip, rt' #) -> disjoint llt lt' && disjoint lrt rt'
  _                   -> False

{-|
Removes all elements from the first set that are found in the second set.

@since 0.0.1.0
-}
difference :: RangeSet a -> RangeSet a -> RangeSet a
difference Tip _ = Tip
difference t Tip = t
difference (Fork _ ll lu llt lrt) (Fork _ rl ru rlt rrt) = case splitFork rl ru ll lu llt lrt of
  (# lt', rt' #) -> disjointMerge lt'lt rt'rt
    where
      !lt'lt = difference lt' rlt
      !rt'rt = difference rt' rrt
