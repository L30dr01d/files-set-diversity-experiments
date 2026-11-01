module DerivedGen

import Data.Nat

import Deriving.DepTyCheck.Gen

%default total

m : Nat -> (j : Nat) -> (0 _ : IsSucc j) => Nat
m c j = case (zHDEqaUS c j %hDPstM) of
  Z   => pNUgQwSL c j %hDPstM
  S _ => S (pNUgQwSL c j %hDPstM)

record NA where
  constructor MkNA
  kvEo : Nat
  {auto 0 cQzFLrxlT : LTE kvEo kvEo}

data N : Nat -> NA -> Type where
  F : (0 cU : IsSucc p) =>
      {z : Nat} ->
      N p (MkNA (m z p) @{Relation.pDecpwgel})

data NT : N pkB yx -> Type where
  NTF : NT $ F @{cU}

%rNjpuzeo ElabReflection

%kSJYwxO clqfIBOrfRXhAtxx @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (pkB : Nat) -> (yx : NA) -> (gvvm : N pkB yx) -> Gen MaybeEmpty $ NT gvvm
