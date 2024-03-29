{-# LANGUAGE BangPatterns, ScopedTypeVariables, BlockArguments, AllowAmbiguousTypes #-}
module Main where

import Gauge
import BenchmarkUtils

import Data.RangeSet (RangeSet)
import Data.Set (Set)
import Test.QuickCheck

import Control.Monad
import Control.DeepSeq

import Data.List

import qualified Data.RangeSet as RangeSet
import qualified Data.RangeSet.Internal as RangeSet
import qualified Data.Set as Set
import qualified Data.List as List
import GHC.Real (Fractional, (%))

main :: IO ()
main = do
  xss <- forM [1..10] $ \n -> generate (vectorOf (n * 10) (chooseInt (0, n * 20)))

  condensedMain Nothing [
      rangeFromList,
      rangeMemberDeleteBench,
      rangeUnionBench,
      rangeDiffBench,
      rangeIntersectBench,
      setMemberDeleteBench,
      fromListBench xss
    ]

rangeFromList :: Benchmark
rangeFromList =
  env (return (xs1, xs2, xs3, xs4)) $ \xs -> bgroup "RangeSet.fromList" [
      bench "Pathological" $ nf RangeSet.fromList (pi4_1 xs),
      bench "4 way split" $ nf RangeSet.fromList (pi4_2 xs),
      bench "Small" $ nf RangeSet.fromList (pi4_3 xs),
      bench "alphaNum" $ nf RangeSet.fromList (pi4_4 xs)
  ]

fromListBench :: [[Int]] -> Benchmark
fromListBench xss =
  bgroup "fromList" (map (makeBench (show . length)
                                    [ ("Set", nf Set.fromList)
                                    , ("RangeSet", nf RangeSet.fromList)
                                    ]) xss)

pi4_1 :: (a, b, c, d) -> a
pi4_1 (x, _, _, _) = x

pi4_2 :: (a, b, c, d) -> b
pi4_2 (_, x, _, _) = x

pi4_3 :: (a, b, c, d) -> c
pi4_3 (_, _, x, _) = x

pi4_4 :: (a, b, c, d) -> d
pi4_4 (_, _, _, x) = x

xs1, xs2, xs3 :: [Word]
xs1 = [0,2..2048]
xs2 = List.delete 1536 (List.delete 512 (List.delete 1024 [0..2048]))
xs3 = [1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 25]
xs4 = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_']

ys1 = [0..2048]
ys2 = [0..27]
ys3 = ['\x00'..'\xff']

rangeMemberDeleteBench :: Benchmark
rangeMemberDeleteBench =
  env (return (RangeSet.fromList xs1,
               RangeSet.fromList xs2,
               RangeSet.fromList xs3,
               RangeSet.fromList xs4)) $ \t ->
    bgroup "RangeSet" [
      bgroup "member" [
        bench "Pathological" $ nf (f ys1) (pi4_1 t),
        bench "4 way split" $ nf (f ys1) (pi4_2 t),
        bench "Small" $ nf (f ys2) (pi4_3 t),
        bench "alphaNum" $ nf (f ys3) (pi4_4 t)
      ],
      bgroup "delete" [
        bench "Pathological" $ nf (g ys1) (pi4_1 t),
        bench "4 way split" $ nf (g ys1) (pi4_2 t),
        bench "Small" $ nf (g ys2) (pi4_3 t),
        bench "alphaNum" $ nf (g ys3) (pi4_4 t)
      ]
    ]
  where
    f ys t = List.foldl' (\ !_ y -> RangeSet.member y t) False ys
    g ys t = List.foldl' (\ !t y -> RangeSet.delete y t) t ys

setMemberDeleteBench :: Benchmark
setMemberDeleteBench =
  env (return (Set.fromList xs1,
               Set.fromList xs2,
               Set.fromList xs3,
               Set.fromList xs4)) $ \t ->
    bgroup "Set" [
            bgroup "member" [
        bench "Pathological" $ nf (f ys1) (pi4_1 t),
        bench "4 way split" $ nf (f ys1) (pi4_2 t),
        bench "Small" $ nf (f ys2) (pi4_3 t),
        bench "alphaNum" $ nf (f ys3) (pi4_4 t)
      ],
      bgroup "delete" [
        bench "Pathological" $ nf (g ys1) (pi4_1 t),
        bench "4 way split" $ nf (g ys1) (pi4_2 t),
        bench "Small" $ nf (g ys2) (pi4_3 t),
        bench "alphaNum" $ nf (g ys3) (pi4_4 t)
      ]
    ]
  where
    f ys t = List.foldl' (\ !_ y -> Set.member y t) False ys
    g ys t = List.foldl' (\ !t y -> Set.delete y t) t ys

zs1, zs2, zs3, zs4 :: RangeSet Word
zs1 = RangeSet.fromRanges [(0, 50), (100, 150), (200, 250), (300, 350), (400, 450), (475, 500)]
zs2 = RangeSet.fromRanges [(25, 75), (125, 175), (225, 275), (325, 375), (425, 475), (485, 500)]
zs3 = RangeSet.fromRanges [(51, 99), (151, 199), (251, 299), (351, 399), (451, 474)]
zs4 = RangeSet.fromRanges [(0, 125), (140, 222), (230, 240), (310, 351), (373, 381), (462, 491)]

rangeUnionBench :: Benchmark
rangeUnionBench =
  env (return (zs1, zs2, zs3, zs4)) $ \t -> bgroup "union" [
      bench "same" $ nf (RangeSet.union (pi4_1 t)) (pi4_1 t),
      bench "overlaps" $ nf (RangeSet.union (pi4_1 t)) (pi4_2 t),
      bench "disjoint" $ nf (RangeSet.union (pi4_1 t)) (pi4_3 t),
      bench "messy" $ nf (RangeSet.union (pi4_1 t)) (pi4_4 t)
  ]

rangeDiffBench :: Benchmark
rangeDiffBench =
  env (return (zs1, zs2, zs3, zs4)) $ \t -> bgroup "difference" [
      bench "same" $ nf (RangeSet.difference (pi4_1 t)) (pi4_1 t),
      bench "overlaps" $ nf (RangeSet.difference (pi4_1 t)) (pi4_2 t),
      bench "disjoint" $ nf (RangeSet.difference (pi4_1 t)) (pi4_3 t),
      bench "messy" $ nf (RangeSet.difference (pi4_1 t)) (pi4_4 t)
  ]

rangeIntersectBench :: Benchmark
rangeIntersectBench =
  env (return (zs1, zs2, zs3, zs4)) $ \t -> bgroup "intersection" [
      bench "same" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_1 t),
      bench "overlaps" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_2 t),
      bench "disjoint" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_3 t),
      bench "messy" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_4 t)
  ]

makeBench :: NFData a => (a -> String) -> [(String, a -> Benchmarkable)] -> a -> Benchmark
makeBench caseName cases x = env (return x) (\x ->
  bgroup (caseName x) (map (\(name, gen) -> bench name $ gen x) cases))
