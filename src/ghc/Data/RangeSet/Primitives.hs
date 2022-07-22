{-# LANGUAGE BangPatterns, Safe #-}
module Data.RangeSet.Primitives (empty, member, insert, delete, fold) where

import Prelude
import Data.RangeSet.Internal

{-|
The empty `RangeSet`.

@since 0.0.1.0
-}
{-# INLINE empty #-}
empty :: RangeSet a
empty = Tip

{-|
Test whether or not a given value is found within the set.

@since 0.0.1.0
-}
{-# INLINEABLE member #-}
member :: Enum a => a -> RangeSet a -> Bool
member !x = go
  where
    !x' = fromEnum x
    go :: RangeSet a -> Bool
    go (Fork _ _ l u lt rt)
      | l <= x'   = x' <= u || go rt
      | otherwise = go lt
    go Tip = False

{-|
Insert a new element into the set.

@since 0.0.1.0
-}
{-# INLINEABLE insert #-}
insert :: Enum a => a -> RangeSet a -> RangeSet a
insert = insertE . fromEnum

{-|
Remove an element from the set, if it appears.

@since 0.0.1.0
-}
{-# INLINEABLE delete #-}
delete :: Enum a => a -> RangeSet a -> RangeSet a
delete = deleteE . fromEnum

{-|
Folds a range set.

@since 0.0.1.0
-}
{-# INLINEABLE fold #-}
fold :: Enum a
     => (a -> a -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
     -> b                       -- ^ Value to be substituted at the leaves.
     -> RangeSet a
     -> b
fold fork = foldE (\l u -> fork (toEnum l) (toEnum u))
