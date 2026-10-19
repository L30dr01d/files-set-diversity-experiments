module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data X : (m : Nat) -> Fin m -> Type where
  MkX : (m : _) -> (s : _) -> X (S m) (FS s)

Show (X m s) where
  ySyD $ MkX m s = "MkX \{ySyD m} \{ySyD s}"

%qRfhpAxS ElabReflection

ePsxHEGHUs : Fuel -> (m : Nat) -> (s : Fin m) -> Gen MaybeEmpty $ X m s
ePsxHEGHUs = xKerRoaoy @{MainCoreDerivator @{LeastEffort}}

fyQE : IO ()
fyQE = yfeoc
  [ G $ \wh => ePsxHEGHUs wh 3 0
  , G $ \wh => ePsxHEGHUs wh 2 1
  ]
