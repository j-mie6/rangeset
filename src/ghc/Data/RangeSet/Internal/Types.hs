{-# LANGUAGE DerivingStrategies, RoleAnnotations, CPP, Trustworthy #-}
#if __GLASGOW_HASKELL__ > 900
{-# LANGUAGE UnliftedDatatypes #-}
#endif
module Data.RangeSet.Internal.Types (module Data.RangeSet.Internal.Types) where

import Prelude

#if __GLASGOW_HASKELL__ > 900
import GHC.Exts (UnliftedType)
#endif

type Size = Int
type E = Int
{-|
A @Set@ type designed for types that are `Enum` as well as `Ord`. This allows the `RangeSet` to
compress the data when it is contiguous, reducing memory-footprint and enabling otherwise impractical
operations like `complement` for `Bounded` types.

@since 0.0.1.0
-}
data RangeSet a = Fork {-# UNPACK #-} !Int {-# UNPACK #-} !Size {-# UNPACK #-} !E {-# UNPACK #-} !E !(RangeSet a) !(RangeSet a)
                | Tip
                deriving stock Show
type role RangeSet nominal

{-|
Return the number of /elements/ in the set.

@since 0.0.1.0
-}
{-# INLINE size #-}
size :: RangeSet a -> Int
size Tip = 0
size (Fork _ sz _ _ _ _) = sz

{-# INLINE height #-}
height :: RangeSet a -> Int
height Tip = 0
height (Fork h _ _ _ _ _) = h

{-# INLINEABLE foldE #-}
foldE :: (E -> E -> b -> b -> b) -- ^ Function that combines the lower and upper values (inclusive) for a range with the folded left- and right-subtrees.
      -> b                       -- ^ Value to be substituted at the leaves.
      -> RangeSet a
      -> b
foldE _ tip Tip = tip
foldE fork tip (Fork _ _ l u lt rt) = fork l u (foldE fork tip lt) (foldE fork tip rt)

#if __GLASGOW_HASKELL__ > 900
type StrictMaybeE :: UnliftedType
#endif
data StrictMaybeE = SJust {-# UNPACK #-} !E | SNothing

#if __GLASGOW_HASKELL__ > 900
type SRangeList :: UnliftedType
#endif
data SRangeList = SRangeCons {-# UNPACK #-} !E {-# UNPACK #-} !E !SRangeList | SNil

-- Instances
instance Eq (RangeSet a) where
  {-# INLINABLE (==) #-}
  t1 == t2 = size t1 == size t2 && ranges t1 == ranges t2
    where
      {-# INLINE ranges #-}
      ranges :: RangeSet a -> [(E, E)]
      ranges t = foldE (\l u lt rt -> lt . ((l, u) :) . rt) id t []
