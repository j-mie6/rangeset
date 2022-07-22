{-# LANGUAGE BangPatterns, UnboxedTuples, Safe #-}
module Data.RangeSet.Internal.Extractors (module Data.RangeSet.Internal.Extractors) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.SmartConstructors

{-# INLINEABLE minRange #-}
minRange :: E -> E -> RangeSet a -> (# E, E #)
minRange !l !u Tip                 = (# l, u #)
minRange _  _  (Fork _ _ l u lt _) = minRange l u lt

{-# INLINEABLE maxRange #-}
maxRange :: E -> E -> RangeSet a -> (# E, E #)
maxRange !l !u Tip                 = (# l, u #)
maxRange _  _  (Fork _ _ l u _ rt) = maxRange l u rt

{-# INLINE minDelete #-}
minDelete :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
minDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, Size, RangeSet a #)
    go !sz !l !u Tip !rt = (# l, u, sz - size rt, rt #)
    go sz l u (Fork _ lsz ll lu llt lrt) rt =
      let (# !ml, !mu, !msz, lt' #) = go lsz ll lu llt lrt
      in (# ml, mu, msz, balanceR (sz - msz) l u lt' rt #)

{-# INLINE maxDelete #-}
maxDelete :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
maxDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, Size, RangeSet a #)
    go !sz !l !u !lt Tip = (# l, u, sz - size lt, lt #)
    go sz l u lt (Fork _ rsz rl ru rlt rrt) =
      let (# !ml, !mu, !msz, rt' #) = go rsz rl ru rlt rrt
      in (# ml, mu, msz, balanceL (sz - msz) l u lt rt' #)
