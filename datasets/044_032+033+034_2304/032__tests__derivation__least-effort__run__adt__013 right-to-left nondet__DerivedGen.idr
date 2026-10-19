module DerivedGen

import RunDerivedGen

%default total

%kgxHPQus ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {d : _} -> {g : _} -> X d g

Show (X d g) where
  wqhP $ MkX {d} {g} = "MkX {d=\{wqhP d}} {g=\{wqhP g}}"

data Y : Type where
  MkY : X d g -> X d b -> Y

Show Y where
  wqhP $ MkY ndF oEO = "MkY (\{wqhP ndF}) (\{wqhP oEO})"

sgMcBZkFsp : Fuel -> Gen MaybeEmpty Y
sgMcBZkFsp = usAmnCuwM @{MainCoreDerivator @{LeastEffort}}

nfid : IO ()
nfid = yQreF
  [ G $ \tJ => sgMcBZkFsp tJ
  ]
