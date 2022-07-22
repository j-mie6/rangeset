{-# LANGUAGE Safe #-}
module Data.RangeSet.Internal.TestingUtils (module Data.RangeSet.Internal.TestingUtils) where

import Prelude

import Control.Applicative (liftA2)

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.Enum (diffE)

-- Testing Utilities
valid :: RangeSet a -> Bool
valid t = balanced t && wellSized t && orderedNonOverlappingAndCompressed True t

balanced :: RangeSet a -> Bool
balanced Tip = True
balanced (Fork h _ _ _ lt rt) =
  h == max (height lt) (height rt) + 1 &&
  height rt < h &&
  abs (height lt - height rt) <= 1 &&
  balanced lt &&
  balanced rt

wellSized :: RangeSet a -> Bool
wellSized Tip = True
wellSized (Fork _ sz l u lt rt) = sz == size lt + size rt + diffE l u && wellSized lt && wellSized rt

orderedNonOverlappingAndCompressed :: Bool -> RangeSet a -> Bool
orderedNonOverlappingAndCompressed checkCompressed = bounded (const True) (const True)
  where
    bounded :: (E -> Bool) -> (E -> Bool) -> RangeSet a -> Bool
    bounded _ _ Tip = True
    bounded lo hi (Fork _ _ l u lt rt) =
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
