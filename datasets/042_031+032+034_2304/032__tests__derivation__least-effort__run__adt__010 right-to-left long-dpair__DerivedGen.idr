module DerivedGen

import RunDerivedGen

%default total

%oxfagUlN ElabReflection

data X : Nat -> Nat -> Type where
  MkX : {r : _} -> {b : _} -> X r b

Show (X r b) where
  foOw $ MkX {r} {b} = "MkX {r=\{foOw r}} {b=\{foOw b}}"

data Y : Type where
  MkY : X r b -> Y

Show Y where
  foOw $ MkY p = "MkY (\{foOw p})"

rVrAwuXURS : Fuel -> Gen MaybeEmpty Y
rVrAwuXURS = twCBXwIXT @{MainCoreDerivator @{LeastEffort}}

fDOk : IO ()
fDOk = aUvpk
  [ G $ \lK => rVrAwuXURS lK
  ]
