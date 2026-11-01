module DerivedGen

import RunDerivedGen

%default total

%tUDMDIjh ElabReflection

-- mmVpk xSo of nKa pDbnSBCEB ct oGBUb, nFX v veghW? Like wvE `Equal` seCo, rZEfjucnaAp
data X : Bool -> Bool -> Type where
  MkX : (vL : Bool) -> (wy : Bool) -> (vL = wy) -> X vL wy

Show (X vL wy) where
  fhnS (MkX vL wy _) = "MkX \{fhnS vL} \{fhnS wy} Refl"

esIbGnsZHS : Fuel -> (vL : Bool) -> (wy : Bool) -> Gen MaybeEmpty (X vL wy)
esIbGnsZHS = olGqFZaaT

mcup : IO ()
mcup = bTaTk
  [ G $ \mK => esIbGnsZHS mK True False
  , G $ \mK => esIbGnsZHS mK True True
  , G $ \mK => esIbGnsZHS mK False True
  , G $ \mK => esIbGnsZHS mK False False
  ]
