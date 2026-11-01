module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%wTDIXpgn ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN t t

{e, r : Nat} -> Show (EqualN e r) where
  yjjp ReflN = "ReflN : EqualN \{yjjp e} \{yjjp r}"

fNlEsEZsQv : Fuel -> (e : Nat) -> Gen MaybeEmpty (r ** EqualN e r)
fNlEsEZsQv = xWiWTFiJG @{MainCoreDerivator @{LeastEffort}}

tVsN : IO ()
tVsN = gVsar
  [ G $ \wM => fNlEsEZsQv wM 5
  , G $ \wM => fNlEsEZsQv wM 0
  , G $ \wM => fNlEsEZsQv wM 11
  ]
