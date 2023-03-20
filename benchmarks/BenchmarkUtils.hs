{-# LANGUAGE BangPatterns #-}
module BenchmarkUtils where

import Gauge.Main         (Benchmark, defaultMainWith)
import Gauge.Main.Options (Config(..), defaultConfig, DisplayMode(Condensed), Verbosity(..))

condensedMain :: Maybe FilePath -> [Benchmark] -> IO ()
condensedMain csv = defaultMainWith $ defaultConfig { displayMode = Condensed
                                                    , timeLimit = Just 10--50
                                                    , includeFirstIter = False
                                                    , csvFile = csv
                                                    --, iters = Just 100
                                                    }

nfList :: [a] -> [a]
nfList xs = go xs xs
  where
    go [] xs = xs
    go ((!x) : (!xs)) orig = go xs orig
