{-# LANGUAGE DerivingStrategies, MagicHash, UnboxedTuples, RoleAnnotations, TypeApplications, MultiWayIf #-}
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
    RangeSet(..),
    empty, singleton, null, full, isSingle, extractSingle, size, sizeRanges,
    member, notMember, findMin, findMax,
    insert, delete,
    union, intersection, difference, disjoint, complement,
    isSubsetOf, isProperSubsetOf,
    allLess, allMore,
    elems, unelems, fromRanges, fromDistinctAscRanges, insertRange, fromList, fromDistinctAscList,
    fold,
    -- Testing
    valid
  ) where

import Prelude hiding (null)
import Data.RangeSet.Internal

{-|
The empty `RangeSet`.

@since 2.1.0.0
-}
{-# INLINE empty #-}
empty :: RangeSet a
empty = Tip

{-|
A `RangeSet` containing a single value.

@since 2.1.0.0
-}
singleton :: Enum a => a -> RangeSet a
singleton x = single 1 (fromEnum x) (fromEnum x)

{-|
Is this set empty?

@since 2.1.0.0
-}
null :: RangeSet a -> Bool
null Tip = True
null _ = False

{-|
Is this set full?

@since 2.1.0.0
-}
full :: forall a. (Enum a, Bounded a) => RangeSet a -> Bool
full Tip = False
full (Fork _ _ l u _ _) = l == fromEnum @a minBound && fromEnum @a maxBound == u

{-|
Does this set contain a single element?

@since 2.1.0.0
-}
isSingle :: RangeSet a -> Bool
isSingle (Fork _ 1 _ _ _ _) = True
isSingle _ = False

{-|
Possibly extract the element contained in the set if it is a singleton set.

@since 2.1.0.0
-}
extractSingle :: Enum a => RangeSet a -> Maybe a
extractSingle (Fork _ _ x y Tip Tip) | x == y = Just (toEnum x)
extractSingle _                               = Nothing

{-|
Return the number of /contiguous ranges/ that populate the set.

@since 2.1.0.0
-}
sizeRanges :: forall a. Enum a => RangeSet a -> Int
sizeRanges = fold @a (\_ _ szl szr -> szl + szr + 1) 0

{-|
Test whether or not a given value is found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE member #-}
member :: forall a. Enum a => a -> RangeSet a -> Bool
member !x = go
  where
    !x' = fromEnum x
    go (Fork _ _ l u lt rt)
      | l <= x'   = x' <= u || go rt
      | otherwise = go lt
    go Tip = False

{-|
Test whether or not a given value is not found within the set.

@since 2.1.0.0
-}
{-# INLINEABLE notMember #-}
notMember :: Enum a => a -> RangeSet a -> Bool
notMember x = not . member x

{-|
Insert a new element into the set.

@since 2.1.0.0
-}
{-# INLINEABLE insert #-}
insert :: Enum a => a -> RangeSet a -> RangeSet a
insert = insertE . fromEnum

{-|
Remove an element from the set, if it appears.

@since 2.1.0.0
-}
{-# INLINEABLE delete #-}
delete :: Enum a => a -> RangeSet a -> RangeSet a
delete = deleteE . fromEnum

{-|
Find the minimum value within the set, if one exists.

@since 2.1.0.0
-}
{-# INLINE findMin #-}
findMin :: Enum a => RangeSet a -> Maybe a
findMin Tip = Nothing
findMin (Fork _ _ l u lt _) = let (# !m, !_ #) = minRange l u lt in Just (toEnum m)

{-|
Find the maximum value within the set, if one exists.

@since 2.1.0.0
-}
{-# INLINE findMax #-}
findMax :: Enum a => RangeSet a -> Maybe a
findMax Tip = Nothing
findMax (Fork _ _ l u _ rt) = let (# !_, !m #) = maxRange l u rt in Just (toEnum m)

{-|
Unions two sets together such that if and only if an element appears in either one of the sets, it
will appear in the result set.

@since 2.1.0.0
-}
{-# INLINABLE union #-}
union :: Enum a => RangeSet a -> RangeSet a -> RangeSet a
union t Tip = t
union Tip t = t
union t@(Fork _ _ l u lt rt) t' = case split l u t' of
  (# lt', rt' #)
    | ltlt' `ptrEq` lt, rtrt' `ptrEq` rt -> t
    | otherwise                          -> link l u ltlt' rtrt'
    where !ltlt' = lt `union` lt'
          !rtrt' = rt `union` rt'

{-|
Intersects two sets such that an element appears in the result if and only if it is present in both
of the provided sets.

@since 2.1.0.0
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
      , lt1lt2 `ptrEq` lt1, rt1rt2 `ptrEq` rt1 -> t1
      | otherwise -> disjointLink sz x y lt1lt2 rt1rt2
    Fork _ sz x y lt' rt' -> disjointLink (sz - size lt' - size rt') x y (disjointMerge lt1lt2 lt') (disjointMerge rt' rt1rt2)
  where
    (# !lt2, !overlap, !rt2 #) = splitOverlap l1 u1 t2
    !lt1lt2 = intersection lt1 lt2
    !rt1rt2 = intersection rt1 rt2

{-|
Do two sets have no elements in common?

@since 2.1.0.0
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

@since 2.1.0.0
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

{-|
Filters a set by removing all values greater than or equal to the given value.

@since 2.1.0.0
-}
{-# INLINEABLE allLess #-}
allLess :: Enum a => a -> RangeSet a -> RangeSet a
allLess = allLessE . fromEnum

{-|
Filters a set by removing all values less than or equal to the given value.

@since 2.1.0.0
-}
{-# INLINEABLE allMore #-}
allMore :: Enum a => a -> RangeSet a -> RangeSet a
allMore = allMoreE . fromEnum

{-|
Inverts a set: every value which was an element is no longer an element, and every value that
was not an element now is. This is only possible on `Bounded` types.

@since 2.1.0.0
-}
{-# INLINEABLE complement #-}
complement :: forall a. (Bounded a, Enum a) => RangeSet a -> RangeSet a
complement Tip = single (diffE minBoundE maxBoundE) minBoundE maxBoundE
  where
    !minBoundE = fromEnum @a minBound
    !maxBoundE = fromEnum @a maxBound
complement t | full t = Tip
complement t@(Fork _ sz l u lt rt) = case maxl of
  SJust x -> unsafeInsertR (diffE x maxBoundE) x maxBoundE t'
  SNothing -> t'
  where
    !minBoundE = fromEnum @a minBound
    !maxBoundE = fromEnum @a maxBound
    (# !minl, !minu, !rest #) = minDelete sz l u lt rt

    -- The complement of a tree is at most 1 larger or smaller than the original
    -- if both min and max are minBound and maxBound, it will shrink
    -- if neither min or max are minBound or maxBound, it will grow
    -- otherwise, the tree will not change size
    -- The insert or shrink will happen at an extremity, and rebalance need only occur along the spine
                       -- this is safe, because we've checked for the maxSet case already
    (# !t', !maxl #) | minl == minBoundE = push (succ minu) rest
                     | otherwise         = push minBoundE t

    safeSucc !x
      | x == maxBoundE = SNothing
      | otherwise      = SJust (succ x)

    -- the argument l should not be altered, it /must/ be the correct lower bound
    -- the return /must/ be the next correct lower bound
    push :: E -> RangeSet a -> (# RangeSet a, StrictMaybe E #)
    push !maxl Tip = (# Tip, SJust maxl #)
    push min (Fork _ _ u max lt Tip) =
      let (# !lt', SJust l #) = push min lt
      in  (# fork l (pred u) lt' Tip, safeSucc max #)
    push min (Fork _ _ u l' lt rt@Fork{}) =
      let (# !lt', SJust l #) = push min lt
          -- this is safe, because we know the right-tree contains elements larger than l'
          (# !rt', !max #) = push (succ l') rt
      in  (# fork l (pred u) lt' rt', max #)

{-|
Tests if all the element of the first set appear in the second, but also that the first and second
sets are not equal.

@since 2.1.0.0
-}
{-# INLINE isProperSubsetOf #-}
isProperSubsetOf :: RangeSet a -> RangeSet a -> Bool
isProperSubsetOf t1 t2 = size t1 < size t2 && uncheckedSubsetOf t1 t2

{-|
Tests if all the elements of the first set appear in the second.

@since 2.1.0.0
-}
{-# INLINEABLE isSubsetOf #-}
isSubsetOf :: RangeSet a -> RangeSet a -> Bool
isSubsetOf t1 t2 = size t1 <= size t2 && uncheckedSubsetOf t1 t2

{-|
Returns all the elements found within the set.

@since 2.1.0.0
-}
{-# INLINE elems #-}
elems :: Enum a => RangeSet a -> [a]
elems t = fold (\l u lt rt -> lt . (range l u ++) . rt) id t []

{-|
Returns all the values that are not found within the set.

@since 2.1.0.0
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

{-|
Constructs a `RangeSet` given a list of ranges.

@since 2.1.0.0
-}
fromRanges :: forall a. Enum a => [(a, a)] -> RangeSet a
fromRanges [] = empty
fromRanges ((x, y):rs) = go rs ey (SRange ex ey :) 1
  where
    !ex = fromEnum x
    !ey = fromEnum y
    go :: [(a, a)] -> E -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] !_ k !n = fromDistinctAscRangesSz (k []) n
    go ((x, y):rs) z k n
      -- ordering and disjointness of the ranges broken
      | ex <= z || ey <= z = insertRangeE ex ey (foldr (uncurry insertRange) (fromDistinctAscRangesSz (k []) n) rs)
      | otherwise          = go rs ey (k . (SRange ex ey :)) (n + 1)
      where
        !ex = fromEnum x
        !ey = fromEnum y

{-|
Constructs a `RangeSet` given a list of ranges that are in ascending order and do not overlap (this is unchecked).

@since 2.2.0.0
-}
fromDistinctAscRanges :: forall a. Enum a => [(a, a)] -> RangeSet a
fromDistinctAscRanges rs = go rs id 0
  where
    go :: [(a, a)] -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] k !n = fromDistinctAscRangesSz (k []) n
    go ((x, y):rs) k n = go rs (k . (SRange (fromEnum x) (fromEnum y) :)) (n + 1)

{-|
Inserts a range into a `RangeSet`.

@since 2.1.0.0
-}
{-# INLINE insertRange #-}
insertRange :: Enum a => a -> a -> RangeSet a -> RangeSet a
insertRange l u t =
  let !le = fromEnum l
      !ue = fromEnum u
  in insertRangeE le ue t

{-|
Builds a `RangeSet` from a given list of elements.

@since 2.1.0.0
-}
fromList :: forall a. Enum a => [a] -> RangeSet a
fromList [] = empty
fromList (x:xs) = go xs (fromEnum x) (fromEnum x) id 1
  where
    go :: [a] -> E -> E -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] !l !u k !n = fromDistinctAscRangesSz (k [SRange l u]) n
    go (!x:xs) l u k n
      -- ordering or uniqueness is broken
      | ex <= u      = insertE ex (foldr insert (fromDistinctAscRangesSz (k [SRange l u]) n) xs)
      -- the current range is expanded
      | ex == succ u = go xs l ex k n
      -- a new range begins
      | otherwise    = go xs ex ex (k . (SRange l u :)) (n + 1)
      where !ex = fromEnum x


-- not sure if this one is any use, it avoids one comparison per element...
{-|
Builds a `RangeSet` from a given list of elements that are in ascending order with no duplicates (this is unchecked).

@since 2.1.0.0
-}
fromDistinctAscList :: forall a. Enum a => [a] -> RangeSet a
fromDistinctAscList [] = empty
fromDistinctAscList (x:xs) = go xs (fromEnum x) (fromEnum x) id 1
  where
    go :: [a] -> E -> E -> ([SRange] -> [SRange]) -> Int -> RangeSet a
    go [] !l !u k !n = fromDistinctAscRangesSz (k [SRange l u]) n
    go (!x:xs) l u k n
      -- the current range is expanded
      | ex == succ u = go xs l ex k n
      -- a new range begins
      | otherwise    = go xs ex ex (k . (SRange l u :)) (n + 1)
      where !ex = fromEnum x

{-|
Folds a range set.

@since 2.1.0.0
-}
{-# INLINEABLE fold #-}
fold :: Enum a
     => (a -> a -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
     -> b                       -- ^ Value to be substituted at the leaves.
     -> RangeSet a
     -> b
fold fork = foldE (\l u -> fork (toEnum l) (toEnum u))
