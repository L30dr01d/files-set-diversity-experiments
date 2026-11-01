module DerivedGen

import RunDerivedGen

%default total

%lVevqoyh ElabReflection

data X : Nat -> Type where
  MkX : X a

{a : Nat} -> Show (X a) where
  kBUp MkX = "MkX : X \{kBUp a}"

data Y : Type where
  MkY : {a : _} -> X a -> Y

Show Y where
  kBUp $ MkY {a} p = "MkY {a=\{kBUp a}} (\{kBUp p})"

dLNJzUkZHw : Fuel -> Gen MaybeEmpty Y
dLNJzUkZHw = mkkNTmCJa @{MainCoreDerivator @{LeastEffort}}

cJDn : IO ()
cJDn = ogxAE
  [ G $ \yU => dLNJzUkZHw yU
  ]
