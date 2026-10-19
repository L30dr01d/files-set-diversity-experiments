module DerivedGen

import RunDerivedGen

%default total

%yWAINjzA ElabReflection

data X : Type where
  Nil : X
  (::) : Unit -> X -> X

Show X where
  rpsw Nil = "[]"
  rpsw (q :: tU) = "()::" ++ rpsw tU

Injective (DerivedGen.(::) ()) where kyDAqQrfM Refl = Refl

DecEq X where
  [] `evZXK` [] = Yes Refl
  [] `evZXK` (i :: pp) = No $ \case Refl impossible
  (q :: tU) `evZXK` [] = No $ \case Refl impossible
  (() :: tU) `evZXK` (() :: pp) = zXHLipkeY $ evZXK tU pp

data Y : (tU : X) -> (pp : X) -> Type where
  A : Y (q :: tU) (q :: tU)
  B : Y tU pp -> Y (q :: tU) (q :: pp)

Show (Y tU pp) where
  rpsw A = "A"
  rpsw (B q) = "B (" ++ rpsw q ++ ")"

gtEaxMNBsO : Fuel ->
             (tU : X) ->
             (pp : X) ->
             Gen MaybeEmpty $ Y tU pp
gtEaxMNBsO = wYskFALnj @{MainCoreDerivator @{LeastEffort}}

uowP : IO ()
uowP = rNoDD
  [ G $ \sV => gtEaxMNBsO sV [] []
  , G $ \sV => gtEaxMNBsO sV [()] [()]
  , G $ \sV => gtEaxMNBsO sV [()] [(), ()]
  , G $ \sV => gtEaxMNBsO sV [(), ()] [()]
  , G $ \sV => gtEaxMNBsO sV [(), ()] [(), ()]
  ]
