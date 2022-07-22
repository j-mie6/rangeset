{-# LANGUAGE UnboxedTuples, BangPatterns, Safe #-}
module Data.RangeSet.SetCrossSet (union, intersection, difference, disjoint) where

import Prelude
import Data.RangeSet.Internal

{-|
Unions two sets together such that if and only if an element appears in either one of the sets, it
will appear in the result set.

@since 0.0.1.0
-}
{-# INLINABLE union #-}
union :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
union t Tip = t
union Tip t = t
union t@(Fork _ _ l u lt rt) t' = case split l u t' of
  (# lt', rt' #)
    | stayedSame lt ltlt', stayedSame rt rtrt' -> t
    | otherwise                                -> link l u ltlt' rtrt'
    where !ltlt' = lt `union` lt'
          !rtrt' = rt `union` rt'

{-|
Intersects two sets such that an element appears in the result if and only if it is present in both
of the provided sets.

@since 0.0.1.0
-}
{-# INLINABLE intersection #-}
intersection :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
intersection Tip _ = Tip
intersection _ Tip = Tip
intersection t1@(Fork _ _ l1 u1 lt1 rt1) t2 =
  case overlap of
    Tip -> disjointMerge lt1lt2 rt1rt2
    Fork 1 sz x y _ _
      | x == l1, y == u1
      , stayedSame lt1 lt1lt2, stayedSame rt1 rt1rt2 -> t1
      | otherwise -> disjointLink sz x y lt1lt2 rt1rt2
    Fork _ sz x y lt' rt' -> disjointLink (sz - size lt' - size rt') x y (disjointMerge lt1lt2 lt') (disjointMerge rt' rt1rt2)
  where
    (# !lt2, !overlap, !rt2 #) = splitOverlap l1 u1 t2
    !lt1lt2 = intersection lt1 lt2
    !rt1rt2 = intersection rt1 rt2

{-|
Do two sets have no elements in common?

@since 0.0.1.0
-}
{-# INLINE disjoint #-}
disjoint :: Enum a => RangeSet a -> RangeSet a -> Bool
disjoint Tip _ = True
disjoint _ Tip = True
disjoint (Fork _ _ l u lt rt) t = case splitOverlap l u t of
  (# lt', Tip, rt' #) -> disjoint lt lt' && disjoint rt rt'
  _                   -> False

{-|
Removes all elements from the first set that are found in the second set.

@since 0.0.1.0
-}
{-# INLINEABLE difference #-}
difference :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
difference Tip _ = Tip
difference t Tip = t
difference t (Fork _ _ l u lt rt) = case split l u t of
  (# lt', rt' #)
    | size lt'lt + size rt'rt == size t -> t
    | otherwise -> disjointMerge lt'lt rt'rt
    where
      !lt'lt = difference lt' lt
      !rt'rt = difference rt' rt
