{-# LANGUAGE BangPatterns, TypeApplications, ScopedTypeVariables, BlockArguments, AllowAmbiguousTypes  #-}
module Main where

import Gauge
import BenchmarkUtils

import Data.RangeSet (RangeSet)
import Data.EnumSet (EnumSet)
import Data.Set (Set)
import Data.Patricia (Patricia)
import qualified Data.RangeSet as RangeSet
import qualified Data.EnumSet as EnumSet
import qualified Data.Patricia as Patricia
import qualified Data.Set as Set

import Control.Monad
import Control.DeepSeq
import Data.List
import System.Random.Shuffle
import System.Random.Stateful

import qualified Data.List as List
import GHC.Real (Fractional, (%))
import Data.Ratio (denominator, numerator)

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
binSize = 100 --for full bench

approxSetSize :: Int
approxSetSize = 1000

fillBins' :: forall a. (Ord a, Enum a, Bounded a, Num a, UniformRange a) => IO [(Rational, [(RangeSet a, Set a, EnumSet a, Patricia a, [a], [a])])]
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
        return (c, map (\xs -> (RangeSet.fromList xs, Set.fromList xs, EnumSet.fromList xs, Patricia.fromList xs, xs, sort xs)) xss)

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

contiguityBench :: forall a. (NFData a, Ord a, Enum a) => [Rational] -> [[(RangeSet a, Set a, EnumSet a, Patricia a, [a], [a])]] -> Benchmark
contiguityBench ratios bins = {-es `deepseq`-} env (return (map unzip6 bins)) $ \dat ->
    bgroup "contiguity" (concatMap (mkBench dat) (zip ratios [0..]))

  where
    --es = elems @a
    mkBench dat (ratio, i) = let ~(rs, ss, es, ps, xss, sxss) = dat !! i in [
        bench ("overhead from (" ++ show ratio ++ ")") $ whnf overheadFromList sxss,
        bench ("rangeset-from (" ++ show ratio ++ ")") $ whnf rangeSetFromList sxss,
        bench ("set-from (" ++ show ratio ++ ")") $ whnf setFromList sxss,
        bench ("set-opt-from (" ++ show ratio ++ ")") $ whnf enumSetFromList sxss,
        bench ("patricia-from (" ++ show ratio ++ ")") $ whnf patriciaFromList sxss,
        --bench ("overhead rangeset-all (" ++ show ratio ++ ")") $ whnf (overheadRangeSetAllMember es) rs,
        --bench ("overhead set-all (" ++ show ratio ++ ")") $ whnf (overheadSetAllMember es) ss,
        --bench ("rangeset-all (" ++ show ratio ++ ")") $ whnf (rangeSetAllMember es) rs,
        --bench ("set-all (" ++ show ratio ++ ")") $ whnf (setAllMember es) ss,
        bench ("overhead union (" ++ show ratio ++ ")") $ whnf overheadSetCrossSet rs,
        bench ("rangeset-union (" ++ show ratio ++ ")") $ whnf rangeSetUnion rs,
        bench ("set-union (" ++ show ratio ++ ")") $ whnf setUnion ss,
        bench ("set-opt-union (" ++ show ratio ++ ")") $ whnf enumSetUnion es,
        bench ("patricia-union (" ++ show ratio ++ ")") $ whnf patriciaUnion ps,
        bench ("overhead intersection (" ++ show ratio ++ ")") $ whnf overheadSetCrossSet rs,
        bench ("rangeset-intersection (" ++ show ratio ++ ")") $ whnf rangeSetIntersection rs,
        bench ("set-intersection (" ++ show ratio ++ ")") $ whnf setIntersection ss,
        bench ("set-opt-intersection (" ++ show ratio ++ ")") $ whnf enumSetIntersection es,
        bench ("patricia-intersection (" ++ show ratio ++ ")") $ whnf patriciaIntersection ps,
        bench ("overhead difference (" ++ show ratio ++ ")") $ whnf overheadSetCrossSet rs,
        bench ("rangeset-difference (" ++ show ratio ++ ")") $ whnf rangeSetDifference rs,
        bench ("set-difference (" ++ show ratio ++ ")") $ whnf setDifference ss,
        bench ("set-opt-difference (" ++ show ratio ++ ")") $ whnf enumSetDifference es,
        bench ("patricia-difference (" ++ show ratio ++ ")") $ whnf patriciaDifference ps,
        bench ("overhead mem (" ++ show ratio ++ ")") $ whnf (uncurry overheadMember) (xss, rs),
        bench ("rangeset-mem (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetMember) (xss, rs),
        bench ("set-mem (" ++ show ratio ++ ")") $ whnf (uncurry setMember) (xss, ss),
        bench ("set-opt-mem (" ++ show ratio ++ ")") $ whnf (uncurry enumSetMember) (xss, es),
        bench ("patricia-mem (" ++ show ratio ++ ")") $ whnf (uncurry patriciaMember) (xss, ps),
        bench ("overhead ins (" ++ show ratio ++ ")") $ whnf overheadInsert xss,
        bench ("rangeset-ins (" ++ show ratio ++ ")") $ whnf rangeSetInsert xss,
        bench ("set-ins (" ++ show ratio ++ ")") $ whnf setInsert xss,
        bench ("set-opt-ins (" ++ show ratio ++ ")") $ whnf enumSetInsert xss,
        bench ("patricia-ins (" ++ show ratio ++ ")") $ whnf patriciaInsert xss,
        bench ("rangeset-ins-sorted (" ++ show ratio ++ ")") $ whnf rangeSetInsert sxss,
        bench ("set-ins-sorted (" ++ show ratio ++ ")") $ whnf setInsert sxss,
        bench ("set-opt-ins-sorted (" ++ show ratio ++ ")") $ whnf enumSetInsert sxss,
        bench ("patricia-ins-sorted (" ++ show ratio ++ ")") $ whnf patriciaInsert sxss,
        bench ("overhead del (" ++ show ratio ++ ")") $ whnf (uncurry overheadDelete) (xss, rs),
        bench ("rangeset-del (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetDelete) (xss, rs),
        bench ("set-del (" ++ show ratio ++ ")") $ whnf (uncurry setDelete) (xss, ss),
        bench ("set-opt-del (" ++ show ratio ++ ")") $ whnf (uncurry enumSetDelete) (xss, es),
        bench ("patricia-del (" ++ show ratio ++ ")") $ whnf (uncurry patriciaDelete) (xss, ps),
        bench ("rangeset-del-sorted (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetDelete) (sxss, rs),
        bench ("set-del-sorted (" ++ show ratio ++ ")") $ whnf (uncurry setDelete) (sxss, ss),
        bench ("set-opt-del-sorted (" ++ show ratio ++ ")") $ whnf (uncurry enumSetDelete) (sxss, es),
        bench ("patricia-del-sorted (" ++ show ratio ++ ")") $ whnf (uncurry patriciaDelete) (sxss, ps)
      ]

    overheadMember xss ys = nfList [False | (y, xs) <- zip ys xss, x <- xs]
    rangeSetMember xss rs = nfList [RangeSet.member x r | (r, xs) <- zip rs xss, x <- xs]
    setMember xss ss = nfList [Set.member x s | (s, xs) <- zip ss xss, x <- xs]
    patriciaMember xss ss = nfList [Patricia.member x s | (s, xs) <- zip ss xss, x <- xs]
    enumSetMember xss ss = nfList [EnumSet.member x s | (s, xs) <- zip ss xss, x <- xs]

    overheadInsert = nfList . map (foldr @[] @a (const id) ())
    rangeSetInsert = nfList . map (foldr @[] @a RangeSet.insert RangeSet.empty)
    setInsert = nfList . map (foldr @[] @a Set.insert Set.empty)
    patriciaInsert = nfList . map (foldr @[] @a Patricia.insert Patricia.empty)
    enumSetInsert = nfList . map (foldr @[] @a EnumSet.insert EnumSet.empty)

    overheadDelete xss ys = nfList $ zipWith (foldr (const id)) ys xss
    rangeSetDelete xss rs = nfList $ zipWith (foldr RangeSet.delete) rs xss
    setDelete xss ss = nfList $ zipWith (foldr Set.delete) ss xss
    patriciaDelete xss rs = nfList $ zipWith (foldr Patricia.delete) rs xss
    enumSetDelete xss ss = nfList $ zipWith (foldr EnumSet.delete) ss xss

    overheadSetCrossSet xs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ const <$> xs' <*> xs'

    rangeSetUnion rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ RangeSet.union <$> rs' <*> rs'
    setUnion ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ Set.union <$> ss' <*> ss'
    patriciaUnion rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ Patricia.union <$> rs' <*> rs'
    enumSetUnion ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ EnumSet.union <$> ss' <*> ss'

    rangeSetIntersection rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ RangeSet.intersection <$> rs' <*> rs'
    setIntersection ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ Set.intersection <$> ss' <*> ss'
    patriciaIntersection rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ Patricia.intersection <$> rs' <*> rs'
    enumSetIntersection ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ EnumSet.intersection <$> ss' <*> ss'

    rangeSetDifference rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ RangeSet.difference <$> rs' <*> rs'
    setDifference ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ Set.difference <$> ss' <*> ss'
    patriciaDifference rs' = {-let rs' = take (binSize `div` 2) rs in -}nfList $ Patricia.difference <$> rs' <*> rs'
    enumSetDifference ss' = {-let ss' = take (binSize `div` 2) ss in -}nfList $ EnumSet.difference <$> ss' <*> ss'

    overheadFromList = nfList . map (const ())
    rangeSetFromList = nfList . map RangeSet.fromList
    setFromList = nfList . map Set.fromList
    patriciaFromList = nfList . map Patricia.fromList
    enumSetFromList = nfList . map EnumSet.fromList

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
