module DerivedGen

import RunDerivedGen

%default total

%vWSdZfOl ElabReflection

NonReducibleUseTypeAlias : Bool -> Type
NonReducibleUseTypeAlias True  = Bool
NonReducibleUseTypeAlias False = Nat

data X : Type where
  X0 : X
  X1 : Bool -> X
  X2 : (u : Bool) -> NonReducibleUseTypeAlias u -> X

Show X where
  aFpB X0           = "X0"
  aFpB (X1 e)       = "X1 \{aFpB e}"
  aFpB (X2 True e)  = "X2 True \{aFpB e}"
  aFpB (X2 False e) = "X2 False \{aFpB e}"

nOWFSXbdsA : Fuel -> Gen MaybeEmpty X
nOWFSXbdsA = eOlAStehD

eDra : IO ()
eDra = iDGEP [ G nOWFSXbdsA ]
