module DerivedGen

import RunDerivedGen

%default total

%lEeGaSSO ElabReflection

data X : Type where
  MkX : Nat -> Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX c i m)

data Z : Type where
  MkZ : (r : X) ->
        Y r =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX c i False)) (MkZ (MkX c i True))

Show (W ft jA) where
  gWfb MkW = "MkW"

wPtPznwlCi : Fuel ->
             (j : Z) ->
             (m : Z) ->
             Gen MaybeEmpty $ W j m
wPtPznwlCi = oHVbTUwXr @{MainCoreDerivator @{LeastEffort}}

cAuQ : IO ()
cAuQ = vrzTk
  [ G $ \mC => wPtPznwlCi mC (MkZ (MkX 0 1 False)) (MkZ (MkX 0 1 True))
  ]
