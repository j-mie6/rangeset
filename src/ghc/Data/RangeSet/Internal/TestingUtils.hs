{-# LANGUAGE Safe #-}
module Data.RangeSet.Internal.TestingUtils (module Data.RangeSet.Internal.TestingUtils) where

import Prelude

import Control.Applicative (liftA2)

import Data.RangeSet.Internal.Types

-- Testing Utilities
valid :: RangeSet a -> Bool
valid t = balanced t && orderedNonOverlappingAndCompressed True t

balanced :: RangeSet a -> Bool
balanced Tip = True
balanced (Fork h _ _ lt rt) =
  h == max (height lt) (height rt) + 1 &&
  height rt < h &&
  abs (height lt - height rt) <= 1 &&
  balanced lt &&
  balanced rt

orderedNonOverlappingAndCompressed :: Bool -> RangeSet a -> Bool
orderedNonOverlappingAndCompressed checkCompressed = bounded (const True) (const True)
  where
    bounded :: (E -> Bool) -> (E -> Bool) -> RangeSet a -> Bool
    bounded _ _ Tip = True
    bounded lo hi (Fork _ l u lt rt) =
      l <= u &&
      lo l &&
      hi u &&
      bounded lo (boundAbove l) lt &&
      bounded (boundBelow u) hi rt

    boundAbove :: E -> E -> Bool
    boundAbove l | checkCompressed = liftA2 (&&) (< l) (< pred l)
                 | otherwise = (< l)

    boundBelow :: E -> E -> Bool
    boundBelow u | checkCompressed = liftA2 (&&) (> u) (> succ u)
                 | otherwise = (> u)
