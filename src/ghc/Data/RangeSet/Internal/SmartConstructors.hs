{-# LANGUAGE BangPatterns #-}
module Data.RangeSet.Internal.SmartConstructors (
    single,
    fork, forkSz, forkH,
    balance, balanceL, balanceR,
    uncheckedBalanceL, uncheckedBalanceR
  ) where

import Prelude
import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.Enum

-- Basic tree constructors
{-# INLINE single #-}
single :: Size -> E -> E -> RangeSet a
single !sz !l !u = Fork 1 sz l u Tip Tip

{-# INLINE heightOfFork #-}
heightOfFork :: Int -> Int -> Int
heightOfFork lh rh = max lh rh + 1

{-# INLINE fork #-}
fork :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = forkSz (size lt + size rt + diffE l u) l u lt rt

--{-# INLINE forkSz #-} -- this does bad things
forkSz :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
forkSz !sz !l !u !lt !rt = forkH sz l u (height lt) lt (height rt) rt

{-# INLINE forkH #-}
forkH :: Size -> E -> E -> Int -> RangeSet a -> Int -> RangeSet a -> RangeSet a
forkH !sz !l !u !lh !lt !rh !rt =  Fork (heightOfFork lh rh) sz l u lt rt

-- Balancers 
{-# NOINLINE balance #-}
balance :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
balance !sz !l !u Tip Tip = single sz l u
balance sz l u lt@(Fork lh lsz ll lu llt lrt) Tip
  | lh == 1   = Fork (lh + 1) sz l u lt Tip
  | otherwise = uncheckedBalanceL sz l u lsz ll lu llt lrt Tip
balance sz l u Tip rt@(Fork rh rsz rl ru rlt rrt)
  | rh == 1   = Fork (rh + 1) sz l u Tip rt
  | otherwise = uncheckedBalanceR sz l u Tip rsz rl ru rlt rrt
balance sz l u lt@(Fork lh lsz ll lu llt lrt) rt@(Fork rh rsz rl ru rlt rrt)
  | height lt > height rt + 1 = uncheckedBalanceL sz l u lsz ll lu llt lrt rt
  | height rt > height lt + 1 = uncheckedBalanceR sz l u lt rsz rl ru rlt rrt
  | otherwise = forkH sz l u lh lt rh rt

{-# INLINEABLE balanceL #-}
balanceL :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL !sz !l1 !u1 lt@(Fork lh lsz l2 u2 llt lrt) !rt
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkH sz l1 u1 lh lt rh rt
  -- The bias is 2 (dltrt == 2)
  | otherwise  = uncheckedBalanceL sz l1 u1 lsz l2 u2 llt lrt rt
  where
    !rh = height rt
    !dltrt = lh - rh
-- If the right shrank (or nothing changed), we have to be prepared to handle the Tip case for lt
balanceL sz l u Tip rt = Fork (height rt + 1) sz l u Tip rt

{-# INLINEABLE balanceR #-}
balanceR :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
balanceR !sz !l1 !u1 !lt rt@(Fork rh rsz l2 u2 rlt rrt)
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkH sz l1 u1 lh lt rh rt
  | otherwise  = uncheckedBalanceR sz l1 u1 lt rsz l2 u2 rlt rrt
  where
    !lh = height lt
    !dltrt = rh - lh
-- If the left shrank (or nothing changed), we have to be prepared to handle the Tip case for rt
balanceR sz l u lt Tip = Fork (height lt + 1) sz l u lt Tip

{-# NOINLINE uncheckedBalanceL #-}
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
uncheckedBalanceL :: Size -> E -> E -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
uncheckedBalanceL !sz !l1 !u1 !szl !l2 !u2 !llt !lrt !rt
  -- The bias is 2 (dltrt == 2)
  | hllt >= hlrt = rotr' sz l1 u1 szl l2 u2 llt lrt rt
  | otherwise    = rotr sz l1 u1 (rotl szl l2 u2 llt lrt) rt
  where
    !hllt = height llt
    !hlrt = height lrt

{-# NOINLINE uncheckedBalanceR #-}
uncheckedBalanceR :: Size -> E -> E -> RangeSet a -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
uncheckedBalanceR !sz !l1 !u1 !lt !szr !l2 !u2 !rlt !rrt
  -- The bias is 2 (drtlt == 2)
  | hrrt >= hrlt = rotl' sz l1 u1 lt szr l2 u2 rlt rrt
  | otherwise    = rotl sz l1 u1 lt (rotr szr l2 u2 rlt rrt)
  where
    !hrlt = height rlt
    !hrrt = height rrt

{-# INLINE rotr #-}
rotr :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotr !sz !l1 !u1 (Fork _ szl l2 u2 p q) !r = rotr' sz l1 u1 szl l2 u2 p q r
rotr _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl !sz !l1 !u1 !p (Fork _ szr l2 u2 q r) = rotl' sz l1 u1 p szr l2 u2 q r
rotl _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotr' #-}
rotr' :: Size -> E -> E -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
rotr' !sz !l1 !u1 !szl !l2 !u2 !p !q !r = forkSz sz l2 u2 p (forkSz (sz - szl + size q) l1 u1 q r)

{-# INLINE rotl' #-}
rotl' :: Size -> E -> E -> RangeSet a -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl' !sz !l1 !u1 !p !szr !l2 !u2 !q !r = forkSz sz l2 u2 (forkSz (sz - szr + size q) l1 u1 p q) r
