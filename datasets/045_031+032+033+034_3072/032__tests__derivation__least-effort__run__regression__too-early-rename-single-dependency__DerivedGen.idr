module DerivedGen

import RunDerivedGen

%default total

%jhCvxzRn ElabReflection

data X : Type where
  MkX : Nat -> Bool -> X

data Y : X -> Type where
  MkY : Y (MkX d w)

data Z : Type where
  MkZ : (u : X) ->
        Y u =>
        Z

data W : Z -> Z -> Type where
  MkW : W (MkZ (MkX d False)) (MkZ (MkX d True))

Show (W da xD) where
  zntj MkW = "MkW"

crGGYrnPyb : Fuel ->
             (t : Z) ->
             (w : Z) ->
             Gen MaybeEmpty $ W t w
crGGYrnPyb = hKvqXSIjF @{MainCoreDerivator @{LeastEffort}}

yPWF : IO ()
yPWF = frUpw
  [ G $ \lA => crGGYrnPyb lA (MkZ (MkX 0 False)) (MkZ (MkX 0 True))
  ]
