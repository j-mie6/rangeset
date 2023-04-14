{-# LANGUAGE BangPatterns, UnboxedTuples, Safe #-}
module Data.RangeSet.Internal.Extractors (module Data.RangeSet.Internal.Extractors) where

import Prelude ()

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.SmartConstructors

{-# INLINEABLE minRange #-}
minRange :: E -> E -> RangeSet a -> (# E, E #)
minRange !l !u Tip               = (# l, u #)
minRange _  _  (Fork _ l u lt _) = minRange l u lt

{-# INLINEABLE maxRange #-}
maxRange :: E -> E -> RangeSet a -> (# E, E #)
maxRange !l !u Tip               = (# l, u #)
maxRange _  _  (Fork _ l u _ rt) = maxRange l u rt

{-# INLINE minDelete #-}
minDelete :: E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
minDelete !l !u !lt !rt = let (# !ml, !mu, t' #) = go l u lt rt in (# ml, mu, t' #)
  where
    go :: E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
    go !l !u Tip !rt = (# l, u, rt #)
    go l u (Fork _ ll lu llt lrt) rt =
      let (# !ml, !mu, lt' #) = go ll lu llt lrt
      in (# ml, mu, balanceR l u lt' rt #)

{-# INLINE maxDelete #-}
maxDelete :: E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
maxDelete !l !u !lt !rt = let (# !ml, !mu, t' #) = go l u lt rt in (# ml, mu, t' #)
  where
    go :: E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
    go !l !u !lt Tip = (# l, u, lt #)
    go l u lt (Fork _ rl ru rlt rrt) =
      let (# !ml, !mu, rt' #) = go rl ru rlt rrt
      in (# ml, mu, balanceL l u lt rt' #)
