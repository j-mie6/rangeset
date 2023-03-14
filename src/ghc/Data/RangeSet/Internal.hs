{-# LANGUAGE MagicHash, UnboxedTuples, MultiWayIf, BangPatterns, CPP, Trustworthy #-}
module Data.RangeSet.Internal (
    module Data.RangeSet.Internal,
    RangeSet(..), E, SRangeList(..), StrictMaybeE(..),
    size, height, foldE,
    module Data.RangeSet.Internal.Enum,
    module Data.RangeSet.Internal.SmartConstructors,
    module Data.RangeSet.Internal.Inserters,
    module Data.RangeSet.Internal.Extractors,
    module Data.RangeSet.Internal.Lumpers,
    module Data.RangeSet.Internal.Splitters,
    module Data.RangeSet.Internal.Heuristics
  ) where

import Prelude

import Data.RangeSet.Internal.Types
import Data.RangeSet.Internal.Enum
import Data.RangeSet.Internal.SmartConstructors
import Data.RangeSet.Internal.Inserters
import Data.RangeSet.Internal.Extractors
import Data.RangeSet.Internal.Lumpers
import Data.RangeSet.Internal.Splitters
import Data.RangeSet.Internal.Heuristics
import Data.Bits (shiftR)

{-# INLINEABLE insertE #-}
insertE :: E -> RangeSet a -> RangeSet a
insertE !x Tip = single x x
insertE x t@(Fork h l u lt rt)
  -- Nothing happens when it's already in range
  | l <= x = if
    | x <= u -> t
  -- If it is adjacent to the upper range, it may fuse
    | x == succ u -> fuseRight h l x lt rt                                         -- we know x > u since x <= l && not x <= u
  -- Otherwise, insert and balance for right
    | otherwise -> ifStayedSame rt (insertE x rt) t (balance l u lt)               -- cannot be biased, because fusion can shrink a tree
  | {- x < l -} otherwise = if
  -- If it is adjacent to the lower, it may fuse
    x == pred l then fuseLeft h x u lt rt                                          -- the equality must be guarded by an existence check
  -- Otherwise, insert and balance for left
                else ifStayedSame lt (insertE x lt) t $ \lt' -> balance l u lt' rt -- cannot be biased, because fusion can shrink a tree
  where
    {-# INLINE fuseLeft #-}
    fuseLeft !h !x !u Tip !rt = Fork h x u Tip rt
    fuseLeft h x u (Fork _ ll lu llt lrt) rt
      | (# !l, !x', lt' #) <- maxDelete ll lu llt lrt
      -- we know there exists an element larger than x'
      -- if x == x' + 1, we fuse (x != x' since that breaks disjointness, x == pred l)
      , x == succ x' = balanceR l u lt' rt
      | otherwise    = Fork h x u lt rt
    {-# INLINE fuseRight #-}
    fuseRight !h !l !x !lt Tip = Fork h l x lt Tip
    fuseRight h l x lt (Fork _ rl ru rlt rrt)
      | (# !x', !u, rt' #) <- minDelete rl ru rlt rrt
      -- we know there exists an element smaller than x'
      -- if x == x' - 1, we fuse (x != x' since that breaks disjointness, as x == succ u)
      , x == pred x' = balanceL l u lt rt'
      | otherwise    = Fork h l x lt rt

{-# INLINEABLE deleteE #-}
deleteE :: E -> RangeSet a -> RangeSet a
deleteE !_ Tip = Tip
deleteE x t@(Fork h l u lt rt) =
  case compare l x of
    -- If its the only part of the range, the node is removed
    EQ | x == u    -> glue lt rt
    -- If it's at an extreme, it shrinks the range
       | otherwise -> Fork h (succ l) u lt rt
    LT -> case compare x u of
    -- If it's at an extreme, it shrinks the range
       EQ          -> Fork h l (pred u) lt rt
    -- Otherwise, if it's still in range, the range undergoes fission
       LT          -> fission l x u lt rt
    -- Otherwise delete and balance for one of the left or right
       GT          -> ifStayedSame rt (deleteE x rt) t $ balance l u lt             -- cannot be biased, because fisson can grow a tree
    GT             -> ifStayedSame lt (deleteE x lt) t $ \lt' -> balance l u lt' rt -- cannot be biased, because fisson can grow a tree
  where
    {- Fission breaks a node into two new ranges
       we'll push the range down into the smallest child, ensuring it's balanced -}
    {-# INLINE fission #-}
    fission :: E -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fission !l1 !x !u2 !lt !rt
      | height lt > height rt = fork l1 u1 lt (unsafeInsertL l2 u2 rt)
      | otherwise = fork l1 u1 (unsafeInsertR l2 u2 lt) rt
      where
        !u1 = pred x
        !l2 = succ x

uncheckedSubsetOf :: RangeSet a -> RangeSet a -> Bool
uncheckedSubsetOf Tip _ = True
uncheckedSubsetOf _ Tip = False
uncheckedSubsetOf (Fork _ l u lt rt) t = case splitOverlap l u t of
  (# lt', Fork 1 x y _ _, rt' #) ->
       x == l && y == u
    && size lt <= size lt' && size rt <= size rt'
    && uncheckedSubsetOf lt lt' && uncheckedSubsetOf rt rt'
  _                                -> False

{-# INLINEABLE fromDistinctAscRangesSz #-}
fromDistinctAscRangesSz :: SRangeList -> Int -> RangeSet a
fromDistinctAscRangesSz rs !n = case go rs 0 (n - 1) of (# t, _ #) -> t
  where
    go :: SRangeList -> Int -> Int -> (# RangeSet a, SRangeList #)
    go rs !i !j
      | i > j     = (# Tip, rs #)
      | otherwise =
        let !mid = (i + j) `shiftR` 1
        in case go rs i (mid - 1) of
             (# lt, rs' #) ->
                let !(SRangeCons l u rs'') = rs'
                in case go rs'' (mid + 1) j of
                      -- there is a height bias to the right, so the height of the right tree is all we need
                      -- perhaps this can be computed though from mid somehow?
                      (# rt, rs''' #) -> (# Fork (height rt + 1) l u lt rt, rs''' #)

{-# INLINE insertRangeE #-}
-- This could be improved, but is OK
insertRangeE :: E -> E -> RangeSet a -> RangeSet a
insertRangeE !l !u t = let (# lt, rt #) = split l u t in link l u lt rt
