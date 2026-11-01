module DerivedGen

import RunDerivedGen

%default total

%alEvQXLL ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {l : _} -> {x : _} -> X l x

Show (X l x) where
  riQC $ MkX {l} {x} = "MkX {l=\{riQC l}} {x=\{riQC x}}"

data Y : Type where
  MkY : X l x -> Y

Show Y where
  riQC $ MkY n = "MkY (\{riQC n})"

pkvwdCJMRf : Fuel -> Gen MaybeEmpty Y
pkvwdCJMRf = upOElvTZN @{MainCoreDerivator @{LeastEffort}}

siQf : IO ()
siQf = tkXfU
  [ G $ \ri => pkvwdCJMRf ri
  ]
