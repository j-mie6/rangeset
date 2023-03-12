{-# LANGUAGE BangPatterns, UnboxedTuples, Safe #-}
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
unsafeInsertL :: E -> E -> RangeSet a -> RangeSet a
unsafeInsertL !l !u = go
  where
    go :: RangeSet a -> RangeSet a
    go Tip = single l u
    go (Fork _ l' u' lt rt) = balanceL l' u' (go lt) rt

{-|
Inserts an range at the right-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertR #-}
unsafeInsertR :: E -> E -> RangeSet a -> RangeSet a
unsafeInsertR !l !u = go
  where
    go :: RangeSet a -> RangeSet a
    go Tip = single l u
    go (Fork _ l' u' lt rt) = balanceR l' u' lt (go rt)

{-# INLINEABLE insertLAdj #-}
insertLAdj :: E -> E -> H -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertLAdj !l !u !th !tl !tu !tlt !trt = case minRange tl tu tlt of
  (# !l', _ #) | l' == succ u -> fuseL l th tl tu tlt trt
               | otherwise    -> balanceL tl tu (unsafeInsertL l u tlt) trt
  where
    {-# INLINEABLE fuseL #-}
    fuseL :: E -> H -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseL !l' !h !l !u lt rt = case lt of
      Tip -> Fork h l' u Tip rt
      Fork lh ll lu llt lrt  -> Fork h l u (fuseL l' lh ll lu llt lrt) rt

{-# INLINEABLE insertRAdj #-}
insertRAdj :: E -> E -> H -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertRAdj !l !u !th !tl !tu !tlt !trt = case maxRange tl tu trt of
  (# _, !u' #) | u' == pred l -> fuseR u th tl tu tlt trt
               | otherwise    -> balanceR tl tu tlt (unsafeInsertR l u trt)
  where
    {-# INLINEABLE fuseR #-}
    fuseR :: E -> H -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseR !u' !h !l !u lt rt = case rt of
      Tip -> Fork h l u' lt Tip
      Fork rh rl ru rlt rrt  -> Fork h l u lt (fuseR u' rh rl ru rlt rrt)
