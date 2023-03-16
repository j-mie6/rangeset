{-# LANGUAGE StandaloneDeriving, DeriveAnyClass, DeriveGeneric, BangPatterns, TypeApplications, ScopedTypeVariables, BlockArguments, AllowAmbiguousTypes, CPP #-}
module Main where

-- #define USE_ENUM

import Gauge
import BenchmarkUtils

import Data.RangeSet (RangeSet)
#ifdef USE_ENUM
import Data.EnumSet (Set)
#else
import Data.Set (Set)
#endif


import Control.Monad
import Control.DeepSeq

--import Data.Array.IO

import Data.List
--import Data.Maybe

--import Data.Bifunctor (bimap)

import Control.Selective (whileS)

import GHC.Generics (Generic)

import System.Random.Shuffle
import System.Random.Stateful

import qualified Data.RangeSet as RangeSet
import qualified Data.RangeSet.Internal as RangeSet
#ifdef USE_ENUM
import qualified Data.EnumSet as Set
#else
import qualified Data.Set as Set
#endif
import qualified Data.List as List
import GHC.Real (Fractional, (%))
import Data.Ratio (denominator, numerator)

deriving instance (Generic a, NFData a) => NFData (RangeSet a)
deriving instance Generic a => Generic (RangeSet a)
deriving instance Generic Int
deriving instance Generic Word
deriving instance Generic Char

main :: IO ()
main = do
  --(ratios, bins) <- unzip <$> fillBins @Word
  (ratios, bins) <- unzip <$> fillBins' @Word
  condensedMain (Just "contiguity.csv") [
      contiguityBench ratios bins
    ]

-- This benchmark generates bunches of random data with a contiguity measure of 0.0 to 1.0
-- this is defined as $1 - m/n$ where $n$ is the number of elements in the set and $m$ the number
-- of ranges. For each of these random sets, each element is queried in turn, and the average
-- time is taken. This comparison is done between the rangeset and the data.set

contiguity :: RangeSet a -> Rational
contiguity s = 1 - fromIntegral (RangeSet.sizeRanges s) % fromIntegral (RangeSet.size s)

numContBins :: Int
numContBins = 20

binSize :: Int
binSize = 50 --100 for full bench

approxSetSize :: Int
approxSetSize = 1000

fillBins' :: forall a. (Ord a, Enum a, Bounded a, Num a, UniformRange a) => IO [(Rational, [(RangeSet a, Set a, [a], [a])])]
fillBins' =
  do let granulation = 1 % fromIntegral numContBins
     let toRatio = (* granulation) . fromIntegral
     let cs = map toRatio [0..numContBins-1]

     forM cs $ \c -> do
        let xs = buildWithContiguity approxSetSize c
        xss <- (xs :) <$> replicateM (binSize-1) do
          xs' <- shuffleM xs
          -- allow the elements to shift so they may overlap partially, or even not at all with those in the original
          -- this is important for good distribution when testing union, intersection, difference but should be
          -- invariant for the other benchmarks
          shift <- uniformRM (0, fromIntegral approxSetSize) globalStdGen :: IO a
          return (map (+ shift) xs')
        return (c, map (\xs -> (RangeSet.fromList xs, Set.fromList xs, xs, sort xs)) xss)

buildWithContiguity :: forall a. (Bounded a, Enum a) => Int -> Rational -> [a]
buildWithContiguity atLeast c = go [minBound @a .. maxBound @a] ranges
  where
    go xs []     = []
    go xs (n:ns) = let (r, xs') = splitAt n xs in r ++ go (tail xs') ns

    ranges = replicate numBig bigSize ++ replicate numSmall smallSize

    w = 1 / (1 - c)
    numElems = fromInteger $ numerator w
    numRangesUnscaled = fromInteger $ denominator w
    (smallSize, numBigUnscaled) = quotRem numElems numRangesUnscaled
    numSmallUnscaled = numRangesUnscaled - numBigUnscaled

    (q, r) = quotRem atLeast (smallSize * numSmallUnscaled + bigSize * numBigUnscaled)
    scale = q + (if r == 0 then 0 else 1)
    numBig = numBigUnscaled * scale
    numSmall = numSmallUnscaled * scale
    bigSize = smallSize + 1

contiguityBench :: forall a. (NFData a, Ord a, Enum a, Generic a) => [Rational] -> [[(RangeSet a, Set a, [a], [a])]] -> Benchmark
contiguityBench ratios bins = {-es `deepseq`-} env (return (map unzip4 bins)) $ \dat ->
    bgroup "contiguity" (concatMap (mkBench dat) (zip ratios [0..]))

  where
    --es = elems @a
    mkBench dat (ratio, i) = let ~(rs, ss, xss, sxss) = dat !! i in [
        bench ("overhead rangeset-from (" ++ show ratio ++ ")") $ whnf overheadRangeSetFromList xss,
        bench ("overhead set-from (" ++ show ratio ++ ")") $ whnf overheadSetFromList xss,
        bench ("rangeset-from (" ++ show ratio ++ ")") $ whnf rangeSetFromList xss,
        bench ("set-from (" ++ show ratio ++ ")") $ whnf setFromList xss,
        --bench ("overhead rangeset-all (" ++ show ratio ++ ")") $ whnf (overheadRangeSetAllMember es) rs,
        --bench ("overhead set-all (" ++ show ratio ++ ")") $ whnf (overheadSetAllMember es) ss,
        --bench ("rangeset-all (" ++ show ratio ++ ")") $ whnf (rangeSetAllMember es) rs,
        --bench ("set-all (" ++ show ratio ++ ")") $ whnf (setAllMember es) ss,
        bench ("overhead rangeset-union (" ++ show ratio ++ ")") $ whnf overheadRangeSetUnion rs,
        bench ("overhead set-union (" ++ show ratio ++ ")") $ whnf overheadSetUnion ss,
        bench ("rangeset-union (" ++ show ratio ++ ")") $ whnf rangeSetUnion rs,
        bench ("set-union (" ++ show ratio ++ ")") $ whnf setUnion ss,
        bench ("overhead rangeset-intersection (" ++ show ratio ++ ")") $ whnf overheadRangeSetIntersection rs,
        bench ("overhead set-intersection (" ++ show ratio ++ ")") $ whnf overheadSetIntersection ss,
        bench ("rangeset-intersection (" ++ show ratio ++ ")") $ whnf rangeSetIntersection rs,
        bench ("set-intersection (" ++ show ratio ++ ")") $ whnf setIntersection ss,
        bench ("overhead rangeset-difference (" ++ show ratio ++ ")") $ whnf overheadRangeSetDifference rs,
        bench ("overhead set-difference (" ++ show ratio ++ ")") $ whnf overheadSetDifference ss,
        bench ("rangeset-difference (" ++ show ratio ++ ")") $ whnf rangeSetDifference rs,
        bench ("set-difference (" ++ show ratio ++ ")") $ whnf setDifference ss,
        bench ("overhead rangeset-mem (" ++ show ratio ++ ")") $ whnf (uncurry overheadRangeSetMember) (xss, rs),
        bench ("overhead set-mem (" ++ show ratio ++ ")") $ whnf (uncurry overheadSetMember) (xss, ss),
        bench ("rangeset-mem (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetMember) (xss, rs),
        bench ("set-mem (" ++ show ratio ++ ")") $ whnf (uncurry setMember) (xss, ss),
        bench ("overhead rangeset-ins (" ++ show ratio ++ ")") $ whnf overheadRangeSetInsert xss,
        bench ("overhead set-ins (" ++ show ratio ++ ")") $ whnf overheadSetInsert xss,
        bench ("rangeset-ins (" ++ show ratio ++ ")") $ whnf rangeSetInsert xss,
        bench ("set-ins (" ++ show ratio ++ ")") $ whnf setInsert xss,
        bench ("rangeset-ins-sorted (" ++ show ratio ++ ")") $ whnf rangeSetInsert sxss,
        bench ("set-ins-sorted (" ++ show ratio ++ ")") $ whnf setInsert sxss,
        bench ("overhead rangeset-del (" ++ show ratio ++ ")") $ whnf (uncurry overheadRangeSetDelete) (xss, rs),
        bench ("overhead set-del (" ++ show ratio ++ ")") $ whnf (uncurry overheadSetDelete) (xss, ss),
        bench ("rangeset-del (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetDelete) (xss, rs),
        bench ("set-del (" ++ show ratio ++ ")") $ whnf (uncurry setDelete) (xss, ss),
        bench ("rangeset-del-sorted (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetDelete) (sxss, rs),
        bench ("set-del-sorted (" ++ show ratio ++ ")") $ whnf (uncurry setDelete) (sxss, ss)
      ]

    overheadRangeSetAllMember :: [a] -> [RangeSet a] -> [Bool]
    overheadRangeSetAllMember !elems rs = nfList [False | r <- rs, x <- elems]

    overheadSetAllMember :: [a] -> [Set a] -> [Bool]
    overheadSetAllMember !elems ss = nfList [False | s <- ss, x <- elems]

    rangeSetAllMember :: [a] -> [RangeSet a] -> [Bool]
    rangeSetAllMember !elems rs = nfList [RangeSet.member x r | r <- rs, x <- elems]

    setAllMember :: [a] -> [Set a] -> [Bool]
    setAllMember !elems ss = nfList [Set.member x s | s <- ss, x <- elems]

    overheadRangeSetMember :: [[a]] -> [RangeSet a] -> [Bool]
    overheadRangeSetMember xss rs = nfList [False | (r, xs) <- zip rs xss, x <- xs]

    overheadSetMember :: [[a]] -> [Set a] -> [Bool]
    overheadSetMember xss ss = nfList [False | (s, xs) <- zip ss xss, x <- xs]

    rangeSetMember :: [[a]] -> [RangeSet a] -> [Bool]
    rangeSetMember xss rs = nfList [RangeSet.member x r | (r, xs) <- zip rs xss, x <- xs]

    setMember :: [[a]] -> [Set a] -> [Bool]
    setMember xss ss = nfList [Set.member x s | (s, xs) <- zip ss xss, x <- xs]

    overheadRangeSetInsert :: [[a]] -> [RangeSet a]
    overheadRangeSetInsert = nfList . map (foldr (const id) RangeSet.empty)

    overheadSetInsert :: [[a]] -> [Set a]
    overheadSetInsert = nfList . map (foldr (const id) Set.empty)

    rangeSetInsert :: [[a]] -> [RangeSet a]
    rangeSetInsert = nfList . map (foldr RangeSet.insert RangeSet.empty)

    setInsert :: [[a]] -> [Set a]
    setInsert = nfList . map (foldr Set.insert Set.empty)

    overheadRangeSetDelete :: [[a]] -> [RangeSet a] -> [RangeSet a]
    overheadRangeSetDelete xss rs = nfList $ zipWith (foldr (const id)) rs xss

    overheadSetDelete :: [[a]] -> [Set a] -> [Set a]
    overheadSetDelete xss ss =  nfList $ zipWith (foldr (const id)) ss xss

    rangeSetDelete :: [[a]] -> [RangeSet a] -> [RangeSet a]
    rangeSetDelete xss rs = nfList $ zipWith (foldr RangeSet.delete) rs xss

    setDelete :: [[a]] -> [Set a] -> [Set a]
    setDelete xss ss = nfList $ zipWith (foldr Set.delete) ss xss

    overheadRangeSetUnion :: [RangeSet a] -> [RangeSet a]
    overheadRangeSetUnion rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ const <$> rs' <*> rs'

    overheadSetUnion :: [Set a] -> [Set a]
    overheadSetUnion ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ const <$> ss' <*> ss'

    rangeSetUnion :: [RangeSet a] -> [RangeSet a]
    rangeSetUnion rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ RangeSet.union <$> rs' <*> rs'

    setUnion :: [Set a] -> [Set a]
    setUnion ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ Set.union <$> ss' <*> ss'

    overheadRangeSetIntersection :: [RangeSet a] -> [RangeSet a]
    overheadRangeSetIntersection rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ const <$> rs' <*> rs'

    overheadSetIntersection :: [Set a] -> [Set a]
    overheadSetIntersection ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ const <$> ss' <*> ss'

    rangeSetIntersection :: [RangeSet a] -> [RangeSet a]
    rangeSetIntersection rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ RangeSet.intersection <$> rs' <*> rs'

    setIntersection :: [Set a] -> [Set a]
    setIntersection ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ Set.intersection <$> ss' <*> ss'

    overheadRangeSetDifference :: [RangeSet a] -> [RangeSet a]
    overheadRangeSetDifference rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ const <$> rs' <*> rs'

    overheadSetDifference :: [Set a] -> [Set a]
    overheadSetDifference ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ const <$> ss' <*> ss'

    rangeSetDifference :: [RangeSet a] -> [RangeSet a]
    rangeSetDifference rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ RangeSet.difference <$> rs' <*> rs'

    setDifference :: [Set a] -> [Set a]
    setDifference ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ Set.difference <$> ss' <*> ss'

    overheadRangeSetFromList :: [[a]] -> [RangeSet a]
    overheadRangeSetFromList = nfList . map (const RangeSet.empty)

    overheadSetFromList :: [[a]] -> [Set a]
    overheadSetFromList = nfList . map (const Set.empty)

    rangeSetFromList :: [[a]] -> [RangeSet a]
    rangeSetFromList = nfList . map RangeSet.fromList

    setFromList :: [[a]] -> [Set a]
    setFromList = nfList . map Set.fromList

{-
maxElem :: Enum a => a
maxElem = toEnum (approxSetSize - 1)

minElem :: Enum a => a
minElem = toEnum 0

elems :: forall a. Enum a => [a]
elems = [minElem @a .. maxElem @a]

fillBins :: forall a. (Ord a, Enum a) => IO [(Rational, [(RangeSet a, Set a, [a], [a])])]
fillBins = do
  bins <- newArray (0, numContBins-1) [] :: IO (IOArray Int [(RangeSet a, [a])])
  let granulation = 1 % fromIntegral numContBins
  let toRatio = (* granulation) . fromIntegral
  let idxs = map toRatio [0..numContBins-1]
  --print idxs

  whileS do
    shuffled <- shuffleM (elems @a)
    let sets = scanr (\x -> bimap (RangeSet.insert x) (x:)) (RangeSet.empty, []) shuffled
    forM_ (init sets) $ \set -> do
      let c = contiguity (fst set)
      let idx = maybe (numContBins-1) (subtract 1) (findIndex (> c) idxs)
      when (RangeSet.sizeRanges (fst set) >= 2) do
        binC <- readArray bins idx
        writeArray bins idx (set : binC)
    szs <- map length <$> getElems bins
    print szs
    return (any (< binSize) szs)

  map (bimap toRatio (map (\(r, xs) -> (r, Set.fromList xs, xs, sort xs)))) <$> getAssocs bins-}
