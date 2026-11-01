module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%qcrMeujZ ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : e `LT2` S (S e)
  Step : e `LT2` d -> e `LT2` S d

nIOJZ : (z, v : Nat) -> LT2 e d -> String
nIOJZ z v Base      = "! \{wZZF z} <<= \{wZZF v}"
nIOJZ z v $ Step iM = ".\{nIOJZ z v iM}"

{z, v : Nat} -> Show (LT2 z v) where
  wZZF = nIOJZ z v

cppzltdlQb : Fuel -> (z, v : Nat) -> Gen MaybeEmpty $ LT2 z v
cppzltdlQb = xXrTfquSh @{MainCoreDerivator @{LeastEffort}}

mjBy : IO ()
mjBy = mycJX
  [ G $ \dZ => cppzltdlQb dZ 0  0
  , G $ \dZ => cppzltdlQb dZ 1  0
  , G $ \dZ => cppzltdlQb dZ 0  1
  , G $ \dZ => cppzltdlQb dZ 1  1
  , G $ \dZ => cppzltdlQb dZ 0  2
  , G $ \dZ => cppzltdlQb dZ 2  0
  , G $ \dZ => cppzltdlQb dZ 2  2
  , G $ \dZ => cppzltdlQb dZ 2  40
  , G $ \dZ => cppzltdlQb dZ 14 23
  , G $ \dZ => cppzltdlQb dZ 23 14
  ]
