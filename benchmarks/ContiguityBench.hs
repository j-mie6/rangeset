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
import Test.QuickCheck

import Control.Monad
import Control.DeepSeq

import Data.Array.IO

import Data.List
import Data.Maybe

import Data.Bifunctor (bimap)

import Control.Selective (whileS)

import GHC.Generics (Generic)

import qualified Data.RangeSet as RangeSet
import qualified Data.RangeSet.Internal as RangeSet
#ifdef USE_ENUM
import qualified Data.EnumSet as Set
#else
import qualified Data.Set as Set
#endif
import qualified Data.List as List
import GHC.Real (Fractional, (%))

deriving instance (Generic a, NFData a) => NFData (RangeSet a)
deriving instance Generic a => Generic (RangeSet a)
deriving instance Generic Int
deriving instance Generic Word
deriving instance Generic Char

main :: IO ()
main = do
  (ratios, bins) <- unzip <$> fillBins @Word
  --print bins

  condensedMain [
      contiguityBench ratios bins
    ]

-- This benchmark generates bunches of random data with a contiguity measure of 0.0 to 1.0
-- this is defined as $1 - m/n$ where $n$ is the number of elements in the set and $m$ the number
-- of ranges. For each of these random sets, each element is queried in turn, and the average
-- time is taken. This comparison is done between the rangeset and the data.set

contiguity :: Enum a => RangeSet a -> Rational
contiguity s = 1 - fromIntegral (RangeSet.sizeRanges s) % fromIntegral (RangeSet.size s)

numContBins :: Int
numContBins = 20

binSize :: Int
binSize = 50

approxSetSize :: Int
approxSetSize = 100

maxElem :: Enum a => a
maxElem = toEnum (approxSetSize - 1)

minElem :: Enum a => a
minElem = toEnum 0

elems :: forall a. Enum a => [a]
elems = [minElem @a .. maxElem @a]

fillBins :: forall a. (Ord a, Enum a) => IO [(Rational, [(RangeSet a, Set a, [a])])]
fillBins = do
  bins <- newArray (0, numContBins-1) [] :: IO (IOArray Int [(RangeSet a, [a])])
  let granulation = 1 % fromIntegral numContBins
  let toRatio = (* granulation) . fromIntegral
  let idxs = map toRatio [0..numContBins-1]
  --print idxs

  whileS do
    shuffled <- generate (shuffle (elems @a))
    let sets = scanr (\x -> bimap (RangeSet.insert x) (x:)) (RangeSet.empty, []) shuffled
    forM_ (init sets) $ \set -> do
      let c = contiguity (fst set)
      let idx = fromMaybe 0 (findIndex (>= c) idxs)
      binC <- readArray bins idx
      writeArray bins idx (set : binC)
    szs <- map length <$> getElems bins
    --print szs
    return (any (< binSize) szs)

  map (bimap toRatio (map (\(r, xs) -> (r, Set.fromList xs, sort xs)))) <$> getAssocs bins

shallowForce :: [a] -> [a]
shallowForce xs = go xs xs
  where
    go [] xs = xs
    go ((!x) : (!xs)) orig = go xs orig

contiguityBench :: forall a. (NFData a, Ord a, Enum a, Generic a) => [Rational] -> [[(RangeSet a, Set a, [a])]] -> Benchmark
contiguityBench ratios bins = es `deepseq` env (return (map unzip3 bins)) $ \dat ->
    bgroup "contiguity" (concatMap (mkBench dat) (zip ratios [0..]))

  where
    es = elems @a
    mkBench dat (ratio, i) = let ~(rs, ss, xss) = dat !! i in [
        bench ("overhead rangeset-from (" ++ show ratio ++ ")") $ whnf overheadRangeSetFromList xss,
        bench ("overhead set-from (" ++ show ratio ++ ")") $ whnf overheadSetFromList xss,
        bench ("rangeset-from (" ++ show ratio ++ ")") $ whnf rangeSetFromList xss,
        bench ("set-from (" ++ show ratio ++ ")") $ whnf setFromList xss,
        bench ("overhead rangeset-all (" ++ show ratio ++ ")") $ whnf (overheadRangeSetAllMember es) rs,
        bench ("overhead set-all (" ++ show ratio ++ ")") $ whnf (overheadSetAllMember es) ss,
        bench ("rangeset-all (" ++ show ratio ++ ")") $ whnf (rangeSetAllMember es) rs,
        bench ("set-all (" ++ show ratio ++ ")") $ whnf (setAllMember es) ss,
        bench ("overhead rangeset-mem (" ++ show ratio ++ ")") $ whnf (uncurry overheadRangeSetMember) (xss, rs),
        bench ("overhead set-mem (" ++ show ratio ++ ")") $ whnf (uncurry overheadSetMember) (xss, ss),
        bench ("rangeset-mem (" ++ show ratio ++ ")") $ whnf (uncurry rangeSetMember) (xss, rs),
        bench ("set-mem (" ++ show ratio ++ ")") $ whnf (uncurry setMember) (xss, ss),
        bench ("overhead rangeset-ins (" ++ show ratio ++ ")") $ whnf overheadRangeSetInsert xss,
        bench ("overhead set-ins (" ++ show ratio ++ ")") $ whnf overheadSetInsert xss,
        bench ("rangeset-ins (" ++ show ratio ++ ")") $ whnf rangeSetInsert xss,
        bench ("set-ins (" ++ show ratio ++ ")") $ whnf setInsert xss
      ]

    overheadRangeSetAllMember :: [a] -> [RangeSet a] -> [Bool]
    overheadRangeSetAllMember !elems rs = shallowForce [False | r <- rs, x <- elems]

    overheadSetAllMember :: [a] -> [Set a] -> [Bool]
    overheadSetAllMember !elems ss = shallowForce [False | s <- ss, x <- elems]

    rangeSetAllMember :: [a] -> [RangeSet a] -> [Bool]
    rangeSetAllMember !elems rs = shallowForce [RangeSet.member x r | r <- rs, x <- elems]

    setAllMember :: [a] -> [Set a] -> [Bool]
    setAllMember !elems ss = shallowForce [Set.member x s | s <- ss, x <- elems]

    overheadRangeSetMember :: [[a]] -> [RangeSet a] -> [Bool]
    overheadRangeSetMember xss rs = shallowForce [False | (r, xs) <- zip rs xss, x <- xs]

    overheadSetMember :: [[a]] -> [Set a] -> [Bool]
    overheadSetMember xss ss = shallowForce [False | (s, xs) <- zip ss xss, x <- xs]

    rangeSetMember :: [[a]] -> [RangeSet a] -> [Bool]
    rangeSetMember xss rs = shallowForce [RangeSet.member x r | (r, xs) <- zip rs xss, x <- xs]

    setMember :: [[a]] -> [Set a] -> [Bool]
    setMember xss ss = shallowForce [Set.member x s | (s, xs) <- zip ss xss, x <- xs]

    overheadRangeSetInsert :: [[a]] -> [RangeSet a]
    overheadRangeSetInsert = shallowForce . map (foldr (flip const) RangeSet.empty)

    overheadSetInsert :: [[a]] -> [Set a]
    overheadSetInsert = shallowForce . map (foldr (flip const) Set.empty)

    rangeSetInsert :: [[a]] -> [RangeSet a]
    rangeSetInsert = shallowForce . map (foldr RangeSet.insert RangeSet.empty)

    setInsert :: [[a]] -> [Set a]
    setInsert = shallowForce . map (foldr Set.insert Set.empty)

    overheadRangeSetFromList :: [[a]] -> [RangeSet a]
    overheadRangeSetFromList = shallowForce . map (const RangeSet.empty)

    overheadSetFromList :: [[a]] -> [Set a]
    overheadSetFromList = shallowForce . map (const Set.empty)

    rangeSetFromList :: [[a]] -> [RangeSet a]
    rangeSetFromList = shallowForce . map RangeSet.fromList

    setFromList :: [[a]] -> [Set a]
    setFromList = shallowForce . map Set.fromList

makeBench :: NFData a => (a -> String) -> [(String, a -> Benchmarkable)] -> a -> Benchmark
makeBench caseName cases x = env (return x) (\x ->
  bgroup (caseName x) (map (\(name, gen) -> bench name $ gen x) cases))
