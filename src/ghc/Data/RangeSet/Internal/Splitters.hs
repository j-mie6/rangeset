{-# LANGUAGE BangPatterns, UnboxedTuples, Safe #-}
module Data.RangeSet.Internal.Splitters (module Data.RangeSet.Internal.Splitters) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.SmartConstructors
import Data.RangeSet.Internal.Inserters
import Data.RangeSet.Internal.Lumpers

{-# INLINEABLE allLessE #-}
allLessE :: E -> RangeSet a -> RangeSet a
allLessE !_ Tip = Tip
allLessE x (Fork _ l u lt rt) = case compare x l of
  EQ          -> lt
  LT          -> allLessE x lt
  GT | x <= u -> unsafeInsertR l (pred x) (allLessE x lt)
  GT          -> link l u lt (allLessE x rt)

{-# INLINEABLE allMoreE #-}
allMoreE :: E -> RangeSet a -> RangeSet a
allMoreE !_ Tip = Tip
allMoreE x (Fork _ l u lt rt) = case compare u x of
  EQ          -> rt
  LT          -> allMoreE x rt
  GT | l <= x -> unsafeInsertL (succ x) u (allMoreE x rt)
  GT          -> link l u (allMoreE x lt) rt

{-# INLINEABLE split #-}
split :: E -> E -> RangeSet a -> (# RangeSet a, RangeSet a #)
split !_ !_ Tip = (# Tip, Tip #)
split l u (Fork _ l' u' lt rt)
  | u < l' = let (# !llt, !lgt #) = split l u lt in (# llt, link l' u' lgt rt #)
  | u' < l = let (# !rlt, !rgt #) = split l u rt in (# link l' u' lt rlt, rgt #)
  -- The ranges overlap in some way
  | otherwise = let !lt' = case compare l' l of
                      EQ -> lt
                      LT -> unsafeInsertR l' (pred l) lt
                      GT -> allLessE l lt
                    !rt' = case compare u u' of
                      EQ -> rt
                      LT -> unsafeInsertL (succ u) u' rt
                      GT -> allMoreE u rt
                in (# lt', rt' #)

{-# INLINE splitOverlap #-}
splitOverlap :: E -> E -> RangeSet a -> (# RangeSet a, RangeSet a, RangeSet a #)
splitOverlap !l !u !t = let (# lt', rt' #) = split l u t in (# lt', overlapping l u t, rt' #)

{-# INLINABLE overlapping #-}
overlapping :: E -> E -> RangeSet a -> RangeSet a
overlapping !_ !_ Tip = Tip
overlapping x y (Fork _ l u lt rt) =
  case compare l x of
    -- range is outside to the left
    GT -> let !lt' = {-allMoreEqX-} overlapping x y lt
          in case cmpY of
               -- range is totally outside
               GT -> disjointLink l u lt' rt'
               EQ -> unsafeInsertR l u lt'
               LT | y >= l -> unsafeInsertR l y lt'
               LT          -> lt' {-overlapping x y lt-}
    -- range is inside on the left
    EQ -> case cmpY of
      -- range is outside on the right
      GT -> unsafeInsertL l u rt'
      LT -> t'
      EQ -> single l u
    LT -> case cmpY of
      -- range is outside on the right
      GT | x <= u -> unsafeInsertL x u rt'
      GT          -> rt' {-overlapping x y rt-}
      _           -> t'
  where
    !cmpY = compare y u
    -- leave lazy!
    rt' = {-allLessEqY-} overlapping x y rt
    t' :: RangeSet a
    t' = single x y

    {-allLessEqY Tip = Tip
    allLessEqY (Fork _ sz l u lt rt) = case compare y l of
      EQ         -> unsafeInsertR 1 y y lt
      LT         -> allLessEqY lt
      GT | y < u -> unsafeInsertR (diffE l y) l y (allLessEqY lt)
      GT         -> disjointLink (sz - size lt - size rt) l u lt (allLessEqY rt)

    allMoreEqX Tip = Tip
    allMoreEqX (Fork _ sz l u lt rt) = case compare u x of
      EQ         -> unsafeInsertL 1 x x rt
      LT         -> allMoreEqX rt
      GT | l < x -> unsafeInsertL (diffE x u) x u (allMoreEqX rt)
      GT         -> disjointLink (sz - size lt - size rt) l u (allMoreEqX lt) rt-}
