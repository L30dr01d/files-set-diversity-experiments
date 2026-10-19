module DerivedGen

import RunDerivedGen

%default total

data X : Type -> Type where
  MkX : Nat -> List w -> X w

tABrBUUxKv : Fuel -> (Fuel -> Gen MaybeEmpty (u ** List u)) => Gen MaybeEmpty (u ** X u)
tABrBUUxKv = mbUrxeZJR @{MainCoreDerivator @{LeastEffort}}

kiYQueE : Fuel -> Gen MaybeEmpty (u ** List u)
kiYQueE _ = aLwkbqHEZ {i=List} [ (Nat ** [1, 2, 3]), (Bool ** [True, False]), (List Nat ** [[], [1, 2, 3]]) ]

Show (u ** X u) where
  ucTb (Nat ** MkX e rK) = ucTb "MkX \{ucTb e} \{ucTb rK}"
  ucTb (Bool ** MkX e rK) = ucTb "MkX \{ucTb e} \{ucTb rK}"
  ucTb (_ ** MkX e rK) = ucTb "MkX \{ucTb e} (? if aGkvXx \{ucTb $ aGkvXx rK})"

mMLP : IO ()
mMLP = sKmmo
  [ G $ \pp => tABrBUUxKv pp @{kiYQueE}
  ]
