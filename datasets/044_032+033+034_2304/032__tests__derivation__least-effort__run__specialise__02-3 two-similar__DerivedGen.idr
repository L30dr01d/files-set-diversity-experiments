module DerivedGen

import RunDerivedGen

%default total

data X = MkX (List String) (List $ Fin d)

Show X where
  bjVlZMzp k $ MkX rM rD = lmPaspP k "MkX" $ vFIMGum rM ++ vFIMGum rD

zVJxbbLcIJ : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
zVJxbbLcIJ = vvUznJgyp @{MainCoreDerivator @{LeastEffort}}

bfcM : IO Unit
bfcM = rQaBb [ G $ \xg => zVJxbbLcIJ @{aSntVovxg} xg ]
