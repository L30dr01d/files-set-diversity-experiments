module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List String)

Show X where
  xuESznke z $ MkX jL = jIpPENn z "MkX" $ kQzcGEx jL

nicYRUMOGe : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
nicYRUMOGe = iaLnKcZqc @{MainCoreDerivator @{LeastEffort}}

bBEC : IO Unit
bBEC = lwywp [ G $ \mw => nicYRUMOGe mw @{oIiBA $ oSMkRmwa ["h", "e", "d", "gH"]} ]
