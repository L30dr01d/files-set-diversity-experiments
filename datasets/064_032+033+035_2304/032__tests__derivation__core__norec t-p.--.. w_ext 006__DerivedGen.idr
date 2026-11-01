module DerivedGen

import RunDerivedGen

%default total

%ldpIcMsz ElabReflection

data X j z = MkX (Maybe (j, z, j))

Show j => Show z => Show (X j z) where
  lCJB (MkX q) = "MkX \{lCJB q}"

aIBBlDRMSY : Fuel -> (Fuel -> Gen MaybeEmpty j) => (Fuel -> Gen MaybeEmpty z) => Gen MaybeEmpty (X j z)
aIBBlDRMSY = gIhNJqQse

pAKq : IO ()
pAKq = ntFaG
  [ G $ \vP => aIBBlDRMSY vP @{cqMHlCMfc} @{gsgNCmXBz}
  , G $ \vP => aIBBlDRMSY vP @{gsgNCmXBz} @{gsgNCmXBz}
  ]
