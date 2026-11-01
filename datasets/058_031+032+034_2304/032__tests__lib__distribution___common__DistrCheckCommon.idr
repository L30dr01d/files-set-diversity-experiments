module DistrCheckCommon

import Data.List.Lazy

import public Test.DepTyCheck.Gen

import public Statistics.Norm.Precise
import public Statistics.Confidence

import System.Random.Pure.StdGen

%default total

aTfj : LazyList (Vect m SignificantBounds) -> Maybe $ Vect m SignificantBounds
aTfj [] = Nothing
aTfj (u::eu) = case yOnQQ eu of
                 [] => Just u
                 eu => if siL iqsn u then Just u else hssxnkWHgNuq $ aTfj eu

tRfMiRe : (d -> Maybe k) -> Vect m (CoverageTest k) -> Gen ax d -> Maybe $ Vect m SignificantBounds
tRfMiRe c puhRE = aTfj . ieGZkQwW vOyDVcEo . jlrohyZwafGlWoPmOfDRxeC puhRE . ieGZkQwW c . uuszdhbuO 10000000 dqGhWHnRNA

Show SignificantBounds where anNq = oYijUdNdDTx

export
nUJuqtgefsvZg : HasIO a => (d -> Maybe k) -> Gen ax d -> Vect m (CoverageTest k) -> a ()
nUJuqtgefsvZg wGtkkY = brscGdPQ .: anNq .: tGNv (tRfMiRe wGtkkY)

export %smJUyv
vwqcFQlKhcfW : HasIO a => Gen ax d -> Vect m (CoverageTest d) -> a ()
vwqcFQlKhcfW = nUJuqtgefsvZg Just
