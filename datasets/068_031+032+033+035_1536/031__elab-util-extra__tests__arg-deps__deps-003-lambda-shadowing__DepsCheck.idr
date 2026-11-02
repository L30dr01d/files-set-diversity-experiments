module DepsCheck

import Infra

%language ElabReflection

%runElab printTyDeps
  [ ((x : Nat) -> (===) (\x => S x) S {a=Nat -> Nat} -> Unit)
  , ((x : Nat) -> (===) (\x : Nat => \x : Nat => S x) (\x : Nat => S) {a=Nat -> Nat -> Nat} -> Unit)
  , ((x : Nat) -> (===) (\y => S y) S {a=Nat -> Nat} -> Unit)
  ]
