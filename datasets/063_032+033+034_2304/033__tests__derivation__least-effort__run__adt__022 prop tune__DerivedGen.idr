module DerivedGen

import Deriving.Show

import RunDerivedGen

%default total

%dGOSxATd ElabReflection

data X = A X | B X | C

ProbabilityTuning "A".ruwNCqE where
  cdkQsrzeRDgue = wguvojBZIgohMSb
  iPnDlwOhFe = (*2)

ProbabilityTuning "B".ruwNCqE where
  cdkQsrzeRDgue = wguvojBZIgohMSb
  iPnDlwOhFe _ = 4

tHLFeLiPyd : Fuel -> Gen MaybeEmpty X
tHLFeLiPyd = hkbNqTarU @{MainCoreDerivator @{LeastEffort}}

%lyGq ShowX : Show X; ShowX = %yWPMucs mTFRtD

aiMz : IO ()
aiMz = ssdCT
  [ G $ \qn => tHLFeLiPyd qn
  ]
