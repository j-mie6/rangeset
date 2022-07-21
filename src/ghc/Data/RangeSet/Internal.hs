{-# LANGUAGE DerivingStrategies, MagicHash, UnboxedTuples, RoleAnnotations, TypeApplications, MultiWayIf #-}
module Data.RangeSet.Internal (module Data.RangeSet.Internal) where

import Control.Applicative (liftA2)
import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)

{-# INLINE ptrEq #-}
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)

{-# INLINE range #-}
range :: Enum a => a -> a -> [a]
range l u = [l..u]

{-# INLINE diffE #-}
diffE :: E -> E -> Size
diffE !l !u = u - l + 1

type Size = Int
type E = Int
{-|
A @Set@ type designed for types that are `Enum` as well as `Ord`. This allows the `RangeSet` to
compress the data when it is contiguous, reducing memory-footprint and enabling otherwise impractical
operations like `complement` for `Bounded` types.

@since 2.1.0.0
-}
data RangeSet a = Fork {-# UNPACK #-} !Int {-# UNPACK #-} !Size {-# UNPACK #-} !E {-# UNPACK #-} !E !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock Show
type role RangeSet nominal

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

{-# INLINE single #-}
single :: Size -> E -> E -> RangeSet a
single !sz !l !u = Fork 1 sz l u Tip Tip

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _ _) = h

{-|
Return the number of /elements/ in the set.

@since 2.1.0.0
-}
{-# INLINE size #-}
size :: RangeSet a -> Int
size Tip = 0
size (Fork _ sz _ _ _ _) = sz

{-# INLINE ifeq #-}
ifeq :: RangeSet a -> RangeSet a -> RangeSet a -> (RangeSet a -> RangeSet a) -> RangeSet a
ifeq !x !x' y f = if size x == size x' then y else f x'

{-# INLINEABLE insertE #-}
insertE :: E -> RangeSet a -> RangeSet a
insertE !x Tip = single 1 x x
insertE x t@(Fork h sz l u lt rt)
  -- Nothing happens when it's already in range
  | l <= x = if
    | x <= u -> t
  -- If it is adjacent to the upper range, it may fuse
    | x == succ u -> fuseRight h (sz + 1) l x lt rt                                 -- we know x > u since x <= l && not x <= u
  -- Otherwise, insert and balance for right
    | otherwise -> ifeq rt (insertE x rt) t (balance (sz + 1) l u lt)               -- cannot be biased, because fusion can shrink a tree
  | {- x < l -} otherwise = if
  -- If it is adjacent to the lower, it may fuse
    x == pred l then fuseLeft h (sz + 1) x u lt rt                                  -- the equality must be guarded by an existence check
  -- Otherwise, insert and balance for left
                else ifeq lt (insertE x lt) t $ \lt' -> balance (sz + 1) l u lt' rt -- cannot be biased, because fusion can shrink a tree
  where
    {-# INLINE fuseLeft #-}
    fuseLeft !h !sz !x !u Tip !rt = Fork h sz x u Tip rt
    fuseLeft h sz x u (Fork _ lsz ll lu llt lrt) rt
      | (# !l, !x', lt' #) <- maxDelete lsz ll lu llt lrt
      -- we know there exists an element larger than x'
      -- if x == x' + 1, we fuse (x != x' since that breaks disjointness, x == pred l)
      , x == succ x' = balanceR sz l u lt' rt
      | otherwise    = Fork h sz x u lt rt
    {-# INLINE fuseRight #-}
    fuseRight !h !sz !l !x !lt Tip = Fork h sz l x lt Tip
    fuseRight h sz l x lt (Fork _ rsz rl ru rlt rrt)
      | (# !x', !u, rt' #) <- minDelete rsz rl ru rlt rrt
      -- we know there exists an element smaller than x'
      -- if x == x' - 1, we fuse (x != x' since that breaks disjointness, as x == succ u)
      , x == pred x' = balanceL sz l u lt rt'
      | otherwise    = Fork h sz l x lt rt

{-# INLINEABLE deleteE #-}
deleteE :: E -> RangeSet a -> RangeSet a
deleteE !_ Tip = Tip
deleteE x t@(Fork h sz l u lt rt) =
  case compare l x of
    -- If its the only part of the range, the node is removed
    EQ | x == u    -> glue (sz - 1) lt rt
    -- If it's at an extreme, it shrinks the range
       | otherwise -> Fork h (sz - 1) (succ l) u lt rt
    LT -> case compare x u of
    -- If it's at an extreme, it shrinks the range
       EQ          -> Fork h (sz - 1) l (pred u) lt rt
    -- Otherwise, if it's still in range, the range undergoes fission
       LT          -> fission (sz - 1) l x u lt rt
    -- Otherwise delete and balance for one of the left or right
       GT          -> ifeq rt (deleteE x rt) t $ balance (sz - 1) l u lt             -- cannot be biased, because fisson can grow a tree
    GT             -> ifeq lt (deleteE x lt) t $ \lt' -> balance (sz - 1) l u lt' rt -- cannot be biased, because fisson can grow a tree
  where
    {- Fission breaks a node into two new ranges
       we'll push the range down into the smallest child, ensuring it's balanced -}
    {-# INLINE fission #-}
    fission !sz !l1 !x !u2 !lt !rt
      | height lt > height rt = forkSz sz l1 u1 lt (unsafeInsertL sz' l2 u2 rt)
      | otherwise = forkSz sz l1 u1 (unsafeInsertR sz' l2 u2 lt) rt
      where
        !u1 = pred x
        !l2 = succ x
        !sz' = diffE l2 u2

{-|
Inserts an range at the left-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertL #-}
unsafeInsertL :: Size -> E -> E -> RangeSet a -> RangeSet a
unsafeInsertL !newSz !l !u = go
  where
    go Tip = single newSz l u
    go (Fork _ sz l' u' lt rt) = balanceL (sz + newSz) l' u' (go lt) rt

{-|
Inserts an range at the right-most position in the tree.
It *must* not overlap with any other range within the tree.
It *must* be /known/ not to exist within the tree.
-}
{-# INLINEABLE unsafeInsertR #-}
unsafeInsertR :: Size -> E -> E -> RangeSet a -> RangeSet a
unsafeInsertR !newSz !l !u = go
  where
    go Tip = single newSz l u
    go (Fork _ sz l' u' lt rt) = balanceR (sz + newSz) l' u' lt (go rt)

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
    go !sz !l !u Tip !rt = (# l, u, sz - size rt, rt #)
    go sz l u (Fork _ lsz ll lu llt lrt) rt =
      let (# !ml, !mu, !msz, lt' #) = go lsz ll lu llt lrt
      in (# ml, mu, msz, balanceR (sz - msz) l u lt' rt #)

{-# INLINE maxDelete #-}
maxDelete :: Size -> E -> E -> RangeSet a -> RangeSet a -> (# E, E, RangeSet a #)
maxDelete !sz !l !u !lt !rt = let (# !ml, !mu, !_, t' #) = go sz l u lt rt in (# ml, mu, t' #)
  where
    go !sz !l !u !lt Tip = (# l, u, sz - size lt, lt #)
    go sz l u lt (Fork _ rsz rl ru rlt rrt) =
      let (# !ml, !mu, !msz, rt' #) = go rsz rl ru rlt rrt
      in (# ml, mu, msz, balanceL (sz - msz) l u lt rt' #)

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
rotr !sz !l1 !u1 (Fork _ !szl !l2 !u2 !p !q) !r = rotr' sz l1 u1 szl l2 u2 p q r
rotr _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotl #-}
rotl :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl !sz !l1 !u1 !p (Fork _ !szr !l2 !u2 !q !r) = rotl' sz l1 u1 p szr l2 u2 q r
rotl _ _ _ _ _ = error "rotr on Tip"

{-# INLINE rotr' #-}
rotr' :: Size -> E -> E -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a -> RangeSet a
rotr' !sz !l1 !u1 !szl !l2 !u2 !p !q !r = forkSz sz l2 u2 p (forkSz (sz - szl + size q) l1 u1 q r)

{-# INLINE rotl' #-}
rotl' :: Size -> E -> E -> RangeSet a -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
rotl' !sz !l1 !u1 !p !szr !l2 !u2 !q !r = forkSz sz l2 u2 (forkSz (sz - szr + size q) l1 u1 p q) r

{-# INLINEABLE insertLAdj #-}
insertLAdj :: Size -> E -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertLAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case minRange tl tu tlt of
  (# !l', _ #) | l' == succ u -> fuseL newSz l th tsz tl tu tlt trt
               | otherwise    -> balanceL (tsz + newSz) tl tu (unsafeInsertL newSz l u tlt) trt
  where
    {-# INLINEABLE fuseL #-}
    fuseL :: Size -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseL !newSz !l' !h !sz !l !u lt rt = case lt of
      Tip -> Fork h (newSz + sz) l' u Tip rt
      Fork lh lsz ll lu llt lrt  -> Fork h (newSz + sz) l u (fuseL newSz l' lh lsz ll lu llt lrt) rt

{-# INLINEABLE insertRAdj #-}
insertRAdj :: Size -> E -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
insertRAdj !newSz !l !u !th !tsz !tl !tu !tlt !trt = case maxRange tl tu trt of
  (# _, !u' #) | u' == pred l -> fuseR newSz u th tsz tl tu tlt trt
               | otherwise    -> balanceR (tsz + newSz) tl tu tlt (unsafeInsertR newSz l u trt)
  where
    {-# INLINEABLE fuseR #-}
    fuseR :: Size -> E -> Int -> Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
    fuseR !newSz !u' !h !sz !l !u lt rt = case rt of
      Tip -> Fork h (newSz + sz) l u' lt Tip
      Fork rh rsz rl ru rlt rrt  -> Fork h (newSz + sz) l u lt (fuseR newSz u' rh rsz rl ru rlt rrt)

{-# INLINABLE link #-}
link :: E -> E -> RangeSet a -> RangeSet a -> RangeSet a
link !l !u Tip Tip = single (diffE l u) l u
link l u Tip (Fork rh rsz rl ru rlt rrt) = insertLAdj (diffE l u) l u rh rsz rl ru rlt rrt
link l u (Fork lh lsz ll lu llt lrt) Tip = insertRAdj (diffE l u) l u lh lsz ll lu llt lrt
link l u lt@(Fork _ lsz ll lu llt lrt) rt@(Fork _ rsz rl ru rlt rrt) =
  disjointLink (diffE l' u') l' u' lt'' rt''
  where
    -- we have to check for fusion up front
    (# !lmaxl, !lmaxu, lt' #) = maxDelete lsz ll lu llt lrt
    (# !rminl, !rminu, rt' #) = minDelete rsz rl ru rlt rrt

    (# !l', !lt'' #) | lmaxu == pred l = (# lmaxl, lt' #)
                     | otherwise       = (# l, lt #)

    (# !u', !rt'' #) | rminl == succ u = (# rminu, rt' #)
                     | otherwise       = (# u, rt #)

{-# INLINEABLE disjointLink #-}
disjointLink :: Size -> E -> E -> RangeSet a -> RangeSet a -> RangeSet a
disjointLink !newSz !l !u Tip rt = unsafeInsertL newSz l u rt
disjointLink newSz l u lt Tip = unsafeInsertR newSz l u lt
disjointLink newSz l u lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (newSz + szl + szr) rl ru (disjointLink newSz l u lt rlt) rrt
  | hr < hl + 1 = balanceR (newSz + szl + szr) ll lu llt (disjointLink newSz l u lrt rt)
  | otherwise   = forkH (newSz + szl + szr) l u hl lt hr rt

-- This version checks for fusion between the two trees to be merged
{-{-# INLINEABLE merge #-}
merge :: (Enum a, Ord a) => RangeSet a -> RangeSet a -> RangeSet a
merge Tip Tip = Tip
merge t Tip = t
merge Tip t = t
merge t1 t2 =
  let (# !_, !u1 #) = unsafeMaxRange t1
      (# !l2, !u2, t2' #) = unsafeMinDelete t2
  in if succ u1 == l2 then unsafeMerge (unsafeFuseR (diffE l2 u2) u2 t1) t2'
     else unsafeMerge t1 t2-}

-- This assumes that the trees are /totally/ disjoint
{-# INLINEABLE disjointMerge #-}
disjointMerge :: RangeSet a -> RangeSet a -> RangeSet a
disjointMerge Tip rt = rt
disjointMerge lt Tip = lt
disjointMerge lt@(Fork hl szl ll lu llt lrt) rt@(Fork hr szr rl ru rlt rrt)
  | hl < hr + 1 = balanceL (szl + szr) rl ru (disjointMerge lt rlt) rrt
  | hr < hl + 1 = balanceR (szl + szr) ll lu llt (disjointMerge lrt rt)
  | otherwise   = glue (szl + szr) lt rt

-- Trees must be balanced with respect to eachother, since we pull from the tallest, no balancing is required
{-# INLINEABLE glue #-}
glue :: Size -> RangeSet a -> RangeSet a -> RangeSet a
glue !_ Tip rt = rt
glue _ lt Tip  = lt
glue sz lt@(Fork lh lsz ll lu llt lrt) rt@(Fork rh rsz rl ru rlt rrt)
  | lh < rh = let (# !l, !u, !rt' #) = minDelete rsz rl ru rlt rrt in forkSz sz l u lt rt'
  | otherwise = let (# !l, !u, !lt' #) = maxDelete lsz ll lu llt lrt in forkSz sz l u lt' rt

{-# INLINEABLE allLessE #-}
allLessE :: E -> RangeSet a -> RangeSet a
allLessE !_ Tip = Tip
allLessE x (Fork _ _ l u lt rt) = case compare x l of
  EQ          -> lt
  LT          -> allLessE x lt
  GT | x <= u -> unsafeInsertR (diffE l (pred x)) l (pred x) (allLessE x lt)
  GT          -> link l u lt (allLessE x rt)

{-# INLINEABLE allMoreE #-}
allMoreE :: E -> RangeSet a -> RangeSet a
allMoreE !_ Tip = Tip
allMoreE x (Fork _ _ l u lt rt) = case compare u x of
  EQ          -> rt
  LT          -> allMoreE x rt
  GT | l <= x -> unsafeInsertL (diffE (succ x) u) (succ x) u (allMoreE x rt)
  GT          -> link l u (allMoreE x lt) rt

{-# INLINEABLE split #-}
split :: E -> E -> RangeSet a -> (# RangeSet a, RangeSet a #)
split !_ !_ Tip = (# Tip, Tip #)
split l u (Fork _ _ l' u' lt rt)
  | u < l' = let (# !llt, !lgt #) = split l u lt in (# llt, link l' u' lgt rt #)
  | u' < l = let (# !rlt, !rgt #) = split l u rt in (# link l' u' lt rlt, rgt #)
  -- The ranges overlap in some way
  | otherwise = let !lt' = case compare l' l of
                      EQ -> lt
                      LT -> unsafeInsertR (diffE l' (pred l)) l' (pred l) lt
                      GT -> allLessE l lt
                    !rt' = case compare u u' of
                      EQ -> rt
                      LT -> unsafeInsertL (diffE (succ u) u') (succ u) u' rt
                      GT -> allMoreE u rt
                in (# lt', rt' #)

{-# INLINE splitOverlap #-}
splitOverlap :: E -> E -> RangeSet a -> (# RangeSet a, RangeSet a, RangeSet a #)
splitOverlap !l !u !t = let (# lt', rt' #) = split l u t in (# lt', overlapping l u t, rt' #)

{-# INLINABLE overlapping #-}
overlapping :: E -> E -> RangeSet a -> RangeSet a
overlapping !_ !_ Tip = Tip
overlapping x y (Fork _ sz l u lt rt) =
  case compare l x of
    -- range is outside to the left
    GT -> let !lt' = {-allMoreEqX-} overlapping x y lt
          in case cmpY of
               -- range is totally outside
               GT -> disjointLink nodeSz l u lt' rt'
               EQ -> unsafeInsertR nodeSz l u lt'
               LT | y >= l -> unsafeInsertR (diffE l y) l y lt'
               LT          -> lt' {-overlapping x y lt-}
    -- range is inside on the left
    EQ -> case cmpY of
      -- range is outside on the right
      GT -> unsafeInsertL nodeSz l u rt'
      LT -> t'
      EQ -> single nodeSz l u
    LT -> case cmpY of
      -- range is outside on the right
      GT | x <= u -> unsafeInsertL (diffE x u) x u rt'
      GT          -> rt' {-overlapping x y rt-}
      _           -> t'
  where
    !cmpY = compare y u
    !nodeSz = sz - size lt - size rt
    -- leave lazy!
    rt' = {-allLessEqY-} overlapping x y rt
    t' = single (diffE x y) x y

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

data StrictMaybe a = SJust !a | SNothing

uncheckedSubsetOf :: RangeSet a -> RangeSet a -> Bool
uncheckedSubsetOf Tip _ = True
uncheckedSubsetOf _ Tip = False
uncheckedSubsetOf (Fork _ _ l u lt rt) t = case splitOverlap l u t of
  (# lt', Fork 1 _ x y _ _, rt' #) ->
       x == l && y == u
    && size lt <= size lt' && size rt <= size rt'
    && uncheckedSubsetOf lt lt' && uncheckedSubsetOf rt rt'
  _                              -> False

data SRange = SRange {-# UNPACK #-} !E {-# UNPACK #-} !E

fromDistinctAscRangesSz :: [SRange] -> Int -> RangeSet a
fromDistinctAscRangesSz rs !n = let (# t, _ #) = go rs 0 (n - 1) in t
  where
    go :: [SRange] -> Int -> Int -> (# RangeSet a, [SRange] #)
    go rs !i !j
      | i > j     = (# Tip, rs #)
      | otherwise =
        let !mid = (i + j) `div` 2
            (# lt, rs' #) = go rs i (mid - 1)
            SRange !l !u : rs'' = rs'
            (# rt, rs''' #) = go rs'' (mid + 1) j
        in (# fork l u lt rt, rs''' #)

{-# INLINE insertRangeE #-}
-- This could be improved, but is OK
insertRangeE :: E -> E -> RangeSet a -> RangeSet a
insertRangeE !l !u t = let (# lt, rt #) = split l u t in link l u lt rt

{-# INLINEABLE foldE #-}
foldE :: (E -> E -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
      -> b                       -- ^ Value to be substituted at the leaves.
      -> RangeSet a
      -> b
foldE _ tip Tip = tip
foldE fork tip (Fork _ _ l u lt rt) = fork l u (foldE fork tip lt) (foldE fork tip rt)

-- Instances
instance Eq (RangeSet a) where
  t1 == t2 = size t1 == size t2 && ranges t1 == ranges t2
    where
      {-# INLINE ranges #-}
      ranges :: RangeSet a -> [(E, E)]
      ranges t = foldE (\l u lt rt -> lt . ((l, u) :) . rt) id t []

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
    bounded _ _ Tip = True
    bounded lo hi (Fork _ _ l u lt rt) =
      l <= u &&
      lo l &&
      hi u &&
      bounded lo (boundAbove l) lt &&
      bounded (boundBelow u) hi rt

    boundAbove l | checkCompressed = liftA2 (&&) (< l) (< pred l)
                 | otherwise = (< l)

    boundBelow u | checkCompressed = liftA2 (&&) (> u) (> succ u)
                 | otherwise = (> u)

