module DepsCheck

import Infra

%language ElabReflection

%runElab printTyDeps
  [ Unit
  , (Nat -> Nat)
  , (Nat -> Nat -> Nat)
  , ({a : Type} -> List a -> Nat)
  ]
