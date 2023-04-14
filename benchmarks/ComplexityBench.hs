{-# LANGUAGE BangPatterns, ScopedTypeVariables, BlockArguments, AllowAmbiguousTypes, CPP #-}
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

xs, ys, zs :: [Int]
xs = [0, 2..99999]
ys = [0, 4..19999]
zs = [2, 6..19999]

chunks :: Int -> [a] -> [[a]]
chunks n xs = reverse (take n (iterate (drop (m `div` n)) xs))
  where m = length xs

main :: IO ()
main = do
  condensedMain (Just "complexity.csv") [
      bgroup "disjoint" [ unionB id ys zs
                        , intersectB id ys zs
                        , differenceB id ys zs
                        ],
      bgroup "overlap"  [ unionB id ys ys
                        , intersectB id ys ys
                        , differenceB id ys ys
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

unionB :: ([Int] -> [Int]) -> [Int] -> [Int] -> Benchmark
unionB = mkBench "RangeSet.union" RangeSet.union

intersectB :: ([Int] -> [Int]) -> [Int] -> [Int] -> Benchmark
intersectB = mkBench "RangeSet.intersection" RangeSet.intersection

differenceB :: ([Int] -> [Int]) -> [Int] -> [Int] -> Benchmark
differenceB = mkBench "RangeSet.difference" RangeSet.difference

{-# INLINE mkBench #-}
mkBench :: String -> (RangeSet Int -> RangeSet Int -> RangeSet Int) -> ([Int] -> [Int]) -> [Int] -> [Int] -> Benchmark
mkBench name f adjust xs ys =
  env dat $ \edat -> bgroup name (map (fbench edat) is)
  where
    !n = 10

    dat :: IO (Array (Int, Int) (RangeSet Int, RangeSet Int))
    dat = do
      xss <- traverse shuffleM (chunks n xs)
      yss <- traverse shuffleM (chunks n ys)
      return $ array rng
        [ ((i, j), (RangeSet.fromList xs, RangeSet.fromList (adjust ys)))
        | (i, xs) <- zip [1..n] xss
        , (j, ys) <- zip [1..n] yss
        ]

    !rng = ((1, 1), (n, n))
    !is = force (range rng)
    !sz = length xs `div` n

    fbench dat ij@(i, j) = bench (show (i * sz, j * sz)) (whnf (uncurry f) (dat ! ij))
