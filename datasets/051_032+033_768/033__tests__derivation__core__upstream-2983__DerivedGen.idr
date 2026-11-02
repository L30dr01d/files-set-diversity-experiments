module DerivedGen

import RunDerivedGen

%default total

%kfxkPVUh ElabReflection

data VectMaybeAnyType : Nat -> Type where
  Nil  : VectMaybeAnyType Z
  (::) : Bool -> VectMaybeAnyType b -> VectMaybeAnyType (S b)

data AtIndex : (b : Nat) -> Bool -> VectMaybeAnyType b -> Type where
  Here  : AtIndex (S b) i (i::cU)

Show (AtIndex b u cU) where
  wuRX _ = "Here"

mSYvbrswfI : Fuel -> (b : Nat) -> (v : Bool) -> (u : VectMaybeAnyType b) -> Gen MaybeEmpty $ AtIndex b v u
mSYvbrswfI = uHogtJEGb @{MainCoreDerivator @{LeastEffort}}

zUTS : IO ()
zUTS = hRPFi
  [ G $ \pR => mSYvbrswfI pR 3 True  [ False, True, True ]
  , G $ \pR => mSYvbrswfI pR 3 False [ False, True, True ]
  ]
