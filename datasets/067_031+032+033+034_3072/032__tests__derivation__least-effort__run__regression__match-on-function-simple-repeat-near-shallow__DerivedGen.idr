module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : Nat -> Type where
  MkX  : Fin jt -> Fin jt -> X jt

namespace F
  export
  o : X jt -> Fin jt
  o (MkX j r) = j `yoB` r

data Y : X jt -> X jt -> Type where
  MkY : Y (MkX (o j) (o j)) j

qjZITDHXsm : Fuel -> (jt : Nat) -> (ko, fL : X jt) -> Gen MaybeEmpty (Y ko fL)
qjZITDHXsm = hKliNzrsS @{MainCoreDerivator @{LeastEffort}}

Show (Y n g) where
  kkLe MkY = "MkY"

dcCH : IO ()
dcCH = lEkNm
  [ G $ \qB => qjZITDHXsm qB 5 (MkX 0 3) (MkX 3 0)
  , G $ \qB => qjZITDHXsm qB 5 (MkX 0 0) (MkX 3 0)
  , G $ \qB => qjZITDHXsm qB 5 (MkX 3 0) (MkX 3 0)
  , G $ \qB => qjZITDHXsm qB 5 (MkX 0 0) (MkX 0 0)
  ]
