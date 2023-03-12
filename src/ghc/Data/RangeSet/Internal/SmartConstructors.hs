{-# LANGUAGE BangPatterns, Safe #-}
module Data.RangeSet.Internal.SmartConstructors (
    single,
    fork, forkH,
    balance, balanceL, balanceR,
    uncheckedBalanceL, uncheckedBalanceR
  ) where

import Prelude
import Data.RangeSet.Internal.Types

-- Basic tree constructors
{-# INLINE single #-}
single :: E -> E -> RangeSet a
single !l !u = Fork 1 l u Tip Tip

{-# INLINE heightOfFork #-}
heightOfFork :: H -> H -> H
heightOfFork lh rh = max lh rh + 1

{-# INLINE fork #-}
fork :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
fork !l !u !lt !rt = forkH l u (height lt) lt (height rt) rt

{-# INLINE forkH #-}
forkH :: E -> E -> H -> RangeSet a -> H -> RangeSet a -> RangeSet a
forkH !l !u !lh !lt !rh !rt =  Fork (heightOfFork lh rh) l u lt rt

-- Balancers
{-# NOINLINE balance #-}
balance :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
balance !l !u Tip Tip = single l u
balance l u lt@(Fork lh ll lu llt lrt) Tip
  | lh == 1   = Fork (lh + 1) l u lt Tip
  | otherwise = uncheckedBalanceL l u ll lu llt lrt Tip
balance l u Tip rt@(Fork rh rl ru rlt rrt)
  | rh == 1   = Fork (rh + 1) l u Tip rt
  | otherwise = uncheckedBalanceR l u Tip rl ru rlt rrt
balance l u lt@(Fork lh ll lu llt lrt) rt@(Fork rh rl ru rlt rrt)
  | height lt > height rt + 1 = uncheckedBalanceL l u ll lu llt lrt rt
  | height rt > height lt + 1 = uncheckedBalanceR l u lt rl ru rlt rrt
  | otherwise = forkH l u lh lt rh rt

{-# INLINEABLE balanceL #-}
balanceL :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
balanceL !l1 !u1 lt@(Fork lh l2 u2 llt lrt) !rt
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkH l1 u1 lh lt rh rt
  -- The bias is 2 (dltrt == 2)
  | otherwise  = uncheckedBalanceL l1 u1 l2 u2 llt lrt rt
  where
    !rh = height rt
    !dltrt = lh - rh
-- If the right shrank (or nothing changed), we have to be prepared to handle the Tip case for lt
balanceL l u Tip rt = Fork (height rt + 1) l u Tip rt

{-# INLINEABLE balanceR #-}
balanceR :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
balanceR !l1 !u1 !lt rt@(Fork rh l2 u2 rlt rrt)
  -- both sides are equal height or off by one
  | dltrt <= 1 = forkH l1 u1 lh lt rh rt
  | otherwise  = uncheckedBalanceR l1 u1 lt l2 u2 rlt rrt
  where
    !lh = height lt
    !dltrt = rh - lh
-- If the left shrank (or nothing changed), we have to be prepared to handle the Tip case for rt
balanceR l u lt Tip = Fork (height lt + 1) l u lt Tip

{-# NOINLINE uncheckedBalanceL #-}
-- PRE: left grew or right shrank, difference in height at most 2 biasing to the left
uncheckedBalanceL :: E -> E -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
uncheckedBalanceL !l1 !u1 !l2 !u2 !llt !lrt !rt
  -- The bias is 2 (dltrt == 2)
  | hllt >= hlrt = rotr' l1 u1 l2 u2 llt lrt rt
  | otherwise    = rotr l1 u1 (rotl l2 u2 llt lrt) rt
  where
    !hllt = height llt
    !hlrt = height lrt

{-# NOINLINE uncheckedBalanceR #-}
uncheckedBalanceR :: E -> E -> RangeSet a -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
-- PRE: left shrank or right grew, difference in height at most 2 biasing to the right
uncheckedBalanceR !l1 !u1 !lt !l2 !u2 !rlt !rrt
  -- The bias is 2 (drtlt == 2)
  | hrrt >= hrlt = rotl' l1 u1 lt l2 u2 rlt rrt
  | otherwise    = rotl l1 u1 lt (rotr l2 u2 rlt rrt)
  where
    !hrlt = height rlt
    !hrrt = height rrt

{-# INLINE rotr #-}
rotr :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotr !l1 !u1 (Fork _ l2 u2 p q) !r = rotr' l1 u1 l2 u2 p q r
rotr _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl !l1 !u1 !p (Fork _ l2 u2 q r) = rotl' l1 u1 p l2 u2 q r
rotl _ _ _ _ = error "rotr on Tip"

{-# INLINE rotr' #-}
rotr' :: E -> E -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
rotr' !l1 !u1 !l2 !u2 !p !q !r = fork l2 u2 p (fork l1 u1 q r)

{-# INLINE rotl' #-}
rotl' :: E -> E -> RangeSet a -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl' !l1 !u1 !p !l2 !u2 !q !r = fork l2 u2 (fork l1 u1 p q) r
