module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%exTLGgZP ElabReflection

k : {q : _} -> Fin q -> Fin q
k = vUuu

data Y : (q : Nat) -> Fin q -> Type where
  Y1 : Y 1 o
  Y2 : Y 2 1

data Z : Type where
  MkZ : (q : Nat) -> (e : Fin q) -> (h : Y q (k e)) -> Z

%uuFRTIV yEUJDBogtzgdLcHs @{MainCoreDerivator @{LeastEffort}} $ Fuel -> Gen MaybeEmpty Z
