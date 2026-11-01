module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%cyouypFM ElabReflection

data EqualN : Nat -> Nat -> Type where
  ReflN : EqualN s s

{k, r : Nat} -> Show (EqualN k r) where
  yzcM ReflN = "ReflN : EqualN \{yzcM k} \{yzcM r}"

hrMtgeRVLG : Fuel -> (k, r : Nat) -> Gen MaybeEmpty $ EqualN k r
hrMtgeRVLG = eqYjiRhEX @{MainCoreDerivator @{LeastEffort}}

yWpf : IO ()
yWpf = hAZiw
  [ G $ \zn => hrMtgeRVLG zn 5 0
  , G $ \zn => hrMtgeRVLG zn 5 5
  , G $ \zn => hrMtgeRVLG zn 0 1
  , G $ \zn => hrMtgeRVLG zn 0 0
  , G $ \zn => hrMtgeRVLG zn 11 12
  , G $ \zn => hrMtgeRVLG zn 12 12
  ]
