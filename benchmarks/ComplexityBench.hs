{-# LANGUAGE StandaloneDeriving, DeriveAnyClass, DeriveGeneric, BangPatterns, TypeApplications, ScopedTypeVariables, BlockArguments, AllowAmbiguousTypes, CPP #-}
module Main where

import Gauge
import BenchmarkUtils

import Data.RangeSet (RangeSet)

import Control.Monad
import Control.DeepSeq
import System.Random.Shuffle

import GHC.Generics (Generic)

import qualified Data.RangeSet as RangeSet
import qualified Data.RangeSet.Internal as RangeSet

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Array

import Data.List (foldl')

deriving instance (Generic a, NFData a) => NFData (RangeSet a)
deriving instance Generic a => Generic (RangeSet a)
deriving instance Generic Int
deriving instance Generic Word
deriving instance Generic Char

xs, ys, zs :: [Int]
xs = [0, 2..99999]
ys = [0, 4..19999]
zs = [2, 6..19999]

chunks :: Int -> [a] -> [[a]]
chunks n xs = reverse (take n (iterate (drop (m `div` n)) xs))
  where m = length xs

main :: IO ()
main = do
  xss <- replicateM 16 (shuffleM xs)
  yss <- replicateM 4 (shuffleM ys)
  zss <- replicateM 4 (shuffleM zs)
  condensedMain [
      insert xss{-,
      delete xss,
      union yss zss-}
    ]

insert :: [[Int]] -> Benchmark
insert xss =
  env (return dat) $ \edat -> bgroup "RangeSet.insert" (map (fbench edat) is)
  where
    !dat = listArray (0, n-1) (map (map prepare) (chunks n xss))
    !is = force (indices dat)
    n = 10
    !sz = length (head xss) `div` n

    fbench dat i = bench (show $ (i + 1) * sz) (whnf insertF (dat ! i))

    prepare (x:xs) = (x, RangeSet.fromList xs)

    insertF = shallowForce . map (uncurry RangeSet.insert)
    nothingF = snd

shallowForce :: [a] -> [a]
shallowForce xs = go xs xs
  where
    go [] xs = xs
    go ((!x) : (!xs)) orig = go xs orig

{-delete :: [[Int]] -> Benchmark
delete xss =
  env (return xss) $ \xss -> bench "RangeSet.delete" (nf deleteF xss)
  where
    deleteF :: [[Int]] -> [RangeSet Int]
    deleteF = map (\xs -> foldl' (flip RangeSet.delete) (RangeSet.fromList xs) xs)

union :: [[Int]] -> [[Int]] -> Benchmark
union yss zss =
  env (return (map RangeSet.fromList yss, map RangeSet.fromList zss)) $ \env ->
    bench "RangeSet.union" (nf (uncurry unionF) env)
  where
    unionF :: [RangeSet Int] -> [RangeSet Int] -> [RangeSet Int]
    unionF yss zss = RangeSet.union <$> yss <*> zss

makeBench :: NFData a => (a -> String) -> [(String, a -> Benchmarkable)] -> a -> Benchmark
makeBench caseName cases x = env (return x) (\x ->
  bgroup (caseName x) (map (\(name, gen) -> bench name $ gen x) cases))-}
