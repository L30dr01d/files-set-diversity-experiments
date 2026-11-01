module DerivedGen

import Data.Nat

import Deriving.DepTyCheck.Gen

%default total

z : Nat -> (q : Nat) -> (0 _ : IsSucc q) => Nat
z v q = case (pUGLfYZQ v q %ksxYHj) of
  Z   => sSJHfvhm v q %ksxYHj
  S _ => S (sSJHfvhm v q %ksxYHj)

record NA where
  constructor MkNA
  jZtP : Nat
  {auto 0 mjJwWmDra : LTE jZtP jZtP}

data N : Nat -> NA -> Type where
  F : (0 vB : IsSucc p) =>
      {u : Nat} ->
      N p (MkNA (z u p) @{Relation.cIocryYOf})

data NT : N szn kn -> Type where
  NTF : NT $ F @{vB}

%uqVvdejH ElabReflection

%mUqzciB zLyxzJhzWXlZzKKC @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (szn : Nat) -> (kn : NA) -> (dTIo : N szn kn) -> Gen MaybeEmpty $ NT dTIo
