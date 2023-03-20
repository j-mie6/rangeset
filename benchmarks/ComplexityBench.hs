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

import Data.List (foldl', transpose)

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
  --xss <- replicateM 16 (shuffleM xs)
  --yss <- replicateM 4 (shuffleM ys)
  --zss <- replicateM 4 (shuffleM zs)

  ys' <- shuffleM ys
  zs' <- shuffleM zs

  condensedMain (Just "complexity.csv") [
      bgroup "disjoint" [ unionB ys' zs'
                        , intersectB ys' zs'
                        , differenceB ys' zs'
                        ]
      bgroup "overlap"  [ unionB ys' ys'
                        , intersectB ys' ys'
                        , differenceB ys' ys'
                        ]
    ]

{-insertB :: [[Int]] -> Benchmark
insertB xss =
  env (return dat) $ \edat -> bgroup "RangeSet.insert" (map (fbench edat) is)
  where
    !dat = listArray (0, n-1) (map (map prepare) (chunks n xss))
    !is = force (indices dat)
    n = 10
    !sz = length (head xss) `div` n

    fbench dat i = bench (show $ (i + 1) * sz) (whnf insertF (dat ! i))

    prepare (x:xs) = (x, RangeSet.fromList xs)

    insertF = nfList . map (uncurry RangeSet.insert)
    nothingF = snd-}

unionB :: [Int] -> [Int] -> Benchmark
unionB = mkBench "RangeSet.union" RangeSet.union

intersectB :: [Int] -> [Int] -> Benchmark
intersectB = mkBench "RangeSet.intersection" RangeSet.intersection

differenceB :: [Int] -> [Int] -> Benchmark
differenceB = mkBench "RangeSet.difference" RangeSet.difference

{-# INLINE mkBench #-}
mkBench :: String -> (RangeSet Int -> RangeSet Int -> RangeSet Int) -> [Int] -> [Int] -> Benchmark
mkBench name f xs ys =
  env (return dat) $ \edat -> bgroup name (map (fbench edat) is)
  where
    dat :: Array (Int, Int) (RangeSet Int, RangeSet Int)
    !dat = array ((0, 0), (n, n)) [((i, j), (x, y)) | (i, x) <- zip [0..n] (RangeSet.singleton (negate 4) : xsc), (j, y) <- zip [0..n] (RangeSet.singleton (negate 2) : ysc)]
    xsc = (map RangeSet.fromList . chunks n) xs
    ysc = (map RangeSet.fromList . chunks n) ys
    !is = force (indices dat)
    n = 10
    !sz = length xs `div` n

    fbench dat ij@(0, 0)    = bench (show (1, 1)) (whnf (uncurry f) (dat ! ij))
    fbench dat ij@(0, j)    = bench (show (1, j * sz)) (whnf (uncurry f) (dat ! ij))
    fbench dat ij@(i, 0) = bench (show (i * sz, 1)) (whnf (uncurry f) (dat ! ij))
    fbench dat ij@(i, j) = bench (show (i * sz, j * sz)) (whnf (uncurry f) (dat ! ij))
