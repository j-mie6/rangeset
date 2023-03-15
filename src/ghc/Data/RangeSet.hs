{-# LANGUAGE MagicHash, UnboxedTuples, TypeApplications, BangPatterns, ScopedTypeVariables, Safe #-}
{-|
Module      : Data.RangeSet
Description : Efficient set for (semi-)contiguous data.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the implementation of an efficient set for contiguous data. It has a much
smaller memory footprint than a @Set@, and can result in asymptotically faster operations.

@since 0.0.1.0
-}
module Data.RangeSet (
    RangeSet,
    module Data.RangeSet.Primitives,
    singleton, null, full, isSingle, extractSingle, size, sizeRanges,
    notMember, findMin, findMax,
    module Data.RangeSet.SetCrossSet, complement,
    isSubsetOf, isProperSubsetOf,
    allLess, allMore,
    elems, unelems,
    module Data.RangeSet.Builders,
  ) where

import Prelude hiding (null)
import Data.RangeSet.Internal
import Data.RangeSet.Builders
import Data.RangeSet.Primitives
import Data.RangeSet.SetCrossSet

{-|
A `RangeSet` containing a single value.

@since 0.0.1.0
-}
singleton :: Enum a => a -> RangeSet a
singleton x = single (fromEnum x) (fromEnum x)

{-|
Is this set empty?

@since 0.0.1.0
-}
null :: RangeSet a -> Bool
null Tip = True
null _ = False

{-|
Is this set full?

@since 0.0.1.0
-}
full :: forall a. (Enum a, Bounded a) => RangeSet a -> Bool
full Tip = False
full (Fork _ l u _ _) = l == fromEnum @a minBound && fromEnum @a maxBound == u

{-|
Does this set contain a single element?

@since 0.0.1.0
-}
isSingle :: RangeSet a -> Bool
isSingle (Fork 1 l u _ _) = l == u
isSingle _ = False

{-|
Possibly extract the element contained in the set if it is a singleton set.

@since 0.0.1.0
-}
extractSingle :: Enum a => RangeSet a -> Maybe a
extractSingle (Fork 1 x y _ _) | x == y = Just (toEnum x)
extractSingle _ = Nothing

{-|
Return the number of /contiguous ranges/ that populate the set.

@since 0.0.1.0
-}
sizeRanges :: RangeSet a -> Int
sizeRanges = foldE (\_ _ szl szr -> szl + szr + 1) 0

{-|
Test whether or not a given value is not found within the set.

@since 0.0.1.0
-}
{-# INLINEABLE notMember #-}
notMember :: Enum a => a -> RangeSet a -> Bool
notMember x = not . member x

{-|
Find the minimum value within the set, if one exists.

@since 0.0.1.0
-}
{-# INLINE findMin #-}
findMin :: Enum a => RangeSet a -> Maybe a
findMin Tip = Nothing
findMin (Fork _ l u lt _) = let (# !m, !_ #) = minRange l u lt in Just (toEnum m)

{-|
Find the maximum value within the set, if one exists.

@since 0.0.1.0
-}
{-# INLINE findMax #-}
findMax :: Enum a => RangeSet a -> Maybe a
findMax Tip = Nothing
findMax (Fork _ l u _ rt) = let (# !_, !m #) = maxRange l u rt in Just (toEnum m)

{-|
Filters a set by removing all values greater than or equal to the given value.

@since 0.0.1.0
-}
{-# INLINEABLE allLess #-}
allLess :: Enum a => a -> RangeSet a -> RangeSet a
allLess = allLessE . fromEnum

{-|
Filters a set by removing all values less than or equal to the given value.

@since 0.0.1.0
-}
{-# INLINEABLE allMore #-}
allMore :: Enum a => a -> RangeSet a -> RangeSet a
allMore = allMoreE . fromEnum

{-|
Inverts a set: every value which was an element is no longer an element, and every value that
was not an element now is. This is only possible on `Bounded` types.

@since 0.0.1.0
-}
{-# INLINEABLE complement #-}
complement :: forall a. (Bounded a, Enum a) => RangeSet a -> RangeSet a
complement Tip = single minBoundE maxBoundE
  where
    !minBoundE = fromEnum @a minBound
    !maxBoundE = fromEnum @a maxBound
complement t | full t = Tip
complement t@(Fork _ l u lt rt) = case maxl of
  SJust x -> unsafeInsertR x maxBoundE t'
  SNothing -> t'
  where
    !minBoundE = fromEnum @a minBound
    !maxBoundE = fromEnum @a maxBound
    (# !minl, !minu, !rest #) = minDelete l u lt rt

    -- The complement of a tree is at most 1 larger or smaller than the original
    -- if both min and max are minBound and maxBound, it will shrink
    -- if neither min or max are minBound or maxBound, it will grow
    -- otherwise, the tree will not change size
    -- The insert or shrink will happen at an extremity, and rebalance need only occur along the spine
                       -- this is safe, because we've checked for the maxSet case already
    !(# !t', !maxl #) | minl == minBoundE = push (succ minu) rest
                      | otherwise         = push minBoundE t

    safeSucc !x
      | x == maxBoundE = SNothing
      | otherwise      = SJust (succ x)

    -- the argument l should not be altered, it /must/ be the correct lower bound
    -- the return /must/ be the next correct lower bound
    push :: E -> RangeSet a -> (# RangeSet a, StrictMaybeE #)
    push !maxl Tip = (# Tip, SJust maxl #)
    push min (Fork _ u max lt Tip) =
      let (# !lt', SJust l #) = push min lt
      in  (# fork l (pred u) lt' Tip, safeSucc max #)
    push min (Fork _ u l' lt rt@Fork{}) =
      let (# !lt', SJust l #) = push min lt
          -- this is safe, because we know the right-tree contains elements larger than l'
          !(# !rt', !max #) = push (succ l') rt
      in  (# fork l (pred u) lt' rt', max #)

{-|
Tests if all the element of the first set appear in the second, but also that the first and second
sets are not equal.

@since 0.0.1.0
-}
{-# INLINE isProperSubsetOf #-}
isProperSubsetOf :: RangeSet a -> RangeSet a -> Bool
isProperSubsetOf t1 t2 = size t1 < size t2 && uncheckedSubsetOf t1 t2

{-|
Tests if all the elements of the first set appear in the second.

@since 0.0.1.0
-}
{-# INLINEABLE isSubsetOf #-}
isSubsetOf :: RangeSet a -> RangeSet a -> Bool
isSubsetOf t1 t2 = size t1 <= size t2 && uncheckedSubsetOf t1 t2

{-|
Returns all the elements found within the set.

@since 0.0.1.0
-}
{-# INLINE elems #-}
elems :: Enum a => RangeSet a -> [a]
elems t = fold (\l u lt rt -> lt . (range l u ++) . rt) id t []

{-|
Returns all the values that are not found within the set.

@since 0.0.1.0
-}
{-# INLINEABLE unelems #-}
unelems :: forall a. (Bounded a, Enum a) => RangeSet a -> [a]
unelems t = foldE fork tip t (fromEnum @a minBound) (fromEnum @a maxBound) []
  where
    fork :: E -> E -> (E -> E -> [a] -> [a]) -> (E -> E -> [a] -> [a]) -> E -> E -> ([a] -> [a])
    fork l' u' lt rt l u = dxs . dys
      where
        dxs | l' == l   = id
            | otherwise = lt l (pred l')
        dys | u == u'   = id
            | otherwise = rt (succ u') u
    tip :: E -> E -> [a] -> [a]
    tip l u = (range (toEnum l) (toEnum u) ++)
