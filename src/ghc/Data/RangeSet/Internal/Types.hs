{-# LANGUAGE DerivingStrategies, RoleAnnotations, CPP, Trustworthy, BangPatterns #-}
#if __GLASGOW_HASKELL__ > 900
{-# LANGUAGE UnliftedDatatypes #-}
#endif
module Data.RangeSet.Internal.Types (module Data.RangeSet.Internal.Types) where

import Prelude

#if __GLASGOW_HASKELL__ > 900
import GHC.Exts (UnliftedType)
#endif

import GHC.Word (Word8)

import Data.RangeSet.Internal.Unsafe

type E = Int
type H = Word8
{-|
A @Set@ type designed for types that are `Enum` as well as `Ord`. This allows the `RangeSet` to
compress the data when it is contiguous, reducing memory-footprint and enabling otherwise impractical
operations like `complement` for `Bounded` types.

@since 0.0.1.0
-}
data RangeSet a = Fork {-# UNPACK #-} !H {-# UNPACK #-} !E {-# UNPACK #-} !E !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock Show
type role RangeSet nominal

{-|
Return the number of /elements/ in the set.

@since 0.0.1.0
-}
{-# INLINE size #-}
size :: RangeSet a -> Int
size = foldE (\l u szl szr -> szl + szr + (u - l + 1)) 0

{-# INLINE height #-}
height :: RangeSet a -> H
height Tip = 0
height (Fork h _ _ _ _) = h

{-# INLINEABLE foldE #-}
foldE :: (E -> E -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
      -> b                       -- ^ Value to be substituted at the leaves.
      -> RangeSet a
      -> b
foldE _ tip Tip = tip
foldE fork tip (Fork _ l u lt rt) = fork l u (foldE fork tip lt) (foldE fork tip rt)

#if __GLASGOW_HASKELL__ > 900
type StrictMaybeE :: UnliftedType
#endif
data StrictMaybeE = SJust {-# UNPACK #-} !E | SNothing

#if __GLASGOW_HASKELL__ > 900
type SRangeList :: UnliftedType
#endif
data SRangeList = SRangeCons {-# UNPACK #-} !E {-# UNPACK #-} !E !SRangeList | SNil

absDiff :: H -> H -> H
absDiff !h1 !h2
  | h1 > h2   = h1 - h2
  | otherwise = h2 - h1

-- Instances
instance Eq (RangeSet a) where
  {-# INLINABLE (==) #-}
  t1 == t2 = ptrEq t1 t2 || (absDiff (height t1) (height t2) <= 1 && ranges t1 == ranges t2)
    where
      {-# INLINE ranges #-}
      ranges :: RangeSet a -> [(E, E)]
      ranges t = foldE (\l u lt rt -> lt . ((l, u) :) . rt) id t []
