{-# LANGUAGE StandaloneDeriving, DeriveAnyClass, DeriveGeneric, BangPatterns #-}
module BenchmarkUtils where

import Gauge.Main         (Benchmark, defaultMainWith)
import Gauge.Main.Options (Config(..), defaultConfig, DisplayMode(Condensed), Verbosity(..))

import GHC.Generics (Generic)

import Data.RangeSet.Internal (RangeSet(..))
import Control.DeepSeq

condensedMain :: Maybe FilePath -> [Benchmark] -> IO ()
condensedMain csv = defaultMainWith $ defaultConfig { displayMode = Condensed
                                                    , timeLimit = Just 60
                                                    , includeFirstIter = False
                                                    , csvFile = csv
                                                    --, iters = Just 100
                                                    }

nfList :: [a] -> [a]
nfList xs = go xs xs
  where
    go [] xs = xs
    go ((!x) : (!xs)) orig = go xs orig

instance NFData (RangeSet a) where
    rnf Tip           = ()
    rnf (Fork _ l u lt rt) = rnf l `seq` rnf u `seq` rnf lt `seq` rnf rt
