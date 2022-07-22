{-# LANGUAGE BangPatterns, ScopedTypeVariables, Safe #-}
module Data.RangeSet.Builders (fromRanges, fromDistinctAscRanges, insertRange, fromList, fromDistinctAscList) where

import Prelude hiding (id, (.))
import Data.RangeSet.Internal
import Data.RangeSet.Primitives

id :: SRangeList -> SRangeList
id ss = ss

(.) :: (SRangeList -> SRangeList) -> (SRangeList -> SRangeList) -> SRangeList -> SRangeList
(f . g) ss = f (g ss)

{-|
Constructs a `RangeSet` given a list of ranges.

@since 0.0.1.0
-}
fromRanges :: forall a. Enum a => [(a, a)] -> RangeSet a
fromRanges [] = Tip
fromRanges ((x, y):rs) = go rs ey (SRangeCons ex ey) 1
  where
    !ex = fromEnum x
    !ey = fromEnum y
    go :: [(a, a)] -> E -> (SRangeList -> SRangeList) -> Int -> RangeSet a
    go [] !_ k !n = fromDistinctAscRangesSz (k SNil) n
    go ((x, y):rs) z k n
      -- ordering and disjointness of the ranges broken
      | ex <= z || ey <= z = insertRangeE ex ey (foldr (uncurry insertRange) (fromDistinctAscRangesSz (k SNil) n) rs)
      | otherwise          = go rs ey (k . SRangeCons ex ey) (n + 1)
      where
        !ex = fromEnum x
        !ey = fromEnum y

{-|
Constructs a `RangeSet` given a list of ranges that are in ascending order and do not overlap (this is unchecked).

@since 0.0.1.0
-}
fromDistinctAscRanges :: forall a. Enum a => [(a, a)] -> RangeSet a
fromDistinctAscRanges rs = go rs id 0
  where
    go :: [(a, a)] -> (SRangeList -> SRangeList) -> Int -> RangeSet a
    go [] k !n = fromDistinctAscRangesSz (k SNil) n
    go ((x, y):rs) k n = go rs (k . SRangeCons (fromEnum x) (fromEnum y)) (n + 1)

{-|
Inserts a range into a `RangeSet`.

@since 0.0.1.0
-}
{-# INLINE insertRange #-}
insertRange :: Enum a => a -> a -> RangeSet a -> RangeSet a
insertRange l u t =
  let !le = fromEnum l
      !ue = fromEnum u
  in insertRangeE le ue t

{-|
Builds a `RangeSet` from a given list of elements.

@since 0.0.1.0
-}
fromList :: forall a. Enum a => [a] -> RangeSet a
fromList [] = Tip
fromList (x:xs) = go xs (fromEnum x) (fromEnum x) id 1
  where
    go :: [a] -> E -> E -> (SRangeList -> SRangeList) -> Int -> RangeSet a
    go [] !l !u k !n = fromDistinctAscRangesSz (k (SRangeCons l u SNil)) n
    go (!x:xs) l u k n
      -- ordering or uniqueness is broken
      | ex <= u      = insertE ex (foldr insert (fromDistinctAscRangesSz (k (SRangeCons l u SNil)) n) xs)
      -- the current range is expanded
      | ex == succ u = go xs l ex k n
      -- a new range begins
      | otherwise    = go xs ex ex (k . SRangeCons l u) (n + 1)
      where !ex = fromEnum x


-- not sure if this one is any use, it avoids one comparison per element...
{-|
Builds a `RangeSet` from a given list of elements that are in ascending order with no duplicates (this is unchecked).

@since 0.0.1.0
-}
fromDistinctAscList :: forall a. Enum a => [a] -> RangeSet a
fromDistinctAscList [] = Tip
fromDistinctAscList (x:xs) = go xs (fromEnum x) (fromEnum x) id 1
  where
    go :: [a] -> E -> E -> (SRangeList -> SRangeList) -> Int -> RangeSet a
    go [] !l !u k !n = fromDistinctAscRangesSz (k (SRangeCons l u SNil)) n
    go (!x:xs) l u k n
      -- the current range is expanded
      | ex == succ u = go xs l ex k n
      -- a new range begins
      | otherwise    = go xs ex ex (k . SRangeCons l u) (n + 1)
      where !ex = fromEnum x
