module DerivedGen

import RunDerivedGen

%default total

%lxzRdMLg ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> X -> Type where
  MkY : Y (MkX x q) (MkX b q)

data Z : Type where
  MkZ : (v : X) ->
        (fI : X) ->
        Y v fI =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX x False) (MkX b False)) (MkZ (MkX x True) (MkX b True))

Show (W pg jU) where
  dgfu MkW = "MkW"

jSByfLBBhP : Fuel ->
             (y : Z) ->
             (q : Z) ->
             Gen MaybeEmpty $ W y q
jSByfLBBhP = xdOBNtVhM @{MainCoreDerivator @{LeastEffort}}

hjOf : IO ()
hjOf = tFyHc
  [ G $ \st => jSByfLBBhP st (MkZ (MkX 0 False) (MkX 1 False)) (MkZ (MkX 0 True) (MkX 1 True))
  ]
