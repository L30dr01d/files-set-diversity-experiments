module DerivedGen

import Data.Vect
import RunDerivedGen

%default total

data X : Nat -> Type where
  MkX : Vect w String -> X w

Show (X w) where
  xQeXxCTZ b $ MkX eY = imTefyc b "MkX" $ gqWxibs eY

ylPudRvpHS : Fuel -> (Fuel -> Gen MaybeEmpty String) => (w : _) -> Gen MaybeEmpty $ X w
ylPudRvpHS = wVDXjhoLu @{MainCoreDerivator @{LeastEffort}}

mTYz : IO Unit
mTYz = xeezt
  [ G $ \fG => ylPudRvpHS @{wrcSuBoFp} fG 0
  , G $ \fG => ylPudRvpHS @{wrcSuBoFp} fG 1
  , G $ \fG => ylPudRvpHS @{wrcSuBoFp} fG 3
  ]
