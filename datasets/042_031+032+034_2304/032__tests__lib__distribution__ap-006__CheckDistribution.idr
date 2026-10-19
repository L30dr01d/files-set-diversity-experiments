module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

m : Bool -> Bool
m = hyFXd True

sllYjEsf : Gen MaybeEmpty Bool
sllYjEsf = yNBF m <*> kBLmx [yNBF True, yNBF False]

gzUjOfpmA : Gen MaybeEmpty Bool
gzUjOfpmA = kBLmx [yNBF m, wGLCI] <*> kBLmx [yNBF True, yNBF False]

cgIwsNwPxH : Gen MaybeEmpty Bool
cgIwsNwPxH = kBLmx [wGLCI, yNBF m] <*> kBLmx [yNBF True, yNBF False]

wCEu : IO ()
wCEu = do
  iqZOIuFFMZFG sllYjEsf   [ lrZqTgPrr 1 (== True) ]
  iqZOIuFFMZFG gzUjOfpmA  [ lrZqTgPrr 1 (== True) ]
  iqZOIuFFMZFG cgIwsNwPxH [ lrZqTgPrr 1 (== True) ]
