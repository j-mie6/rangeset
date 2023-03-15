module BenchmarkUtils where

import Gauge.Main         (Benchmark, defaultMainWith)
import Gauge.Main.Options (Config(..), defaultConfig, DisplayMode(Condensed), Verbosity(..))

condensedMain :: [Benchmark] -> IO ()
condensedMain = defaultMainWith (defaultConfig {displayMode = Condensed, includeFirstIter = False {-, iters = Just 100-}})
