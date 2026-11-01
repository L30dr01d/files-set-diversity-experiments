module ConsApps

import Infra

%default total

%language ElabReflection

export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

%runElab printDeepConsApps $ pure
  [ `(a) @@@ ["a"]
  , `(Nat) @@@ []
  , `(Nat) @@@ ["Nat"]
  , `(Vect n a) @@@ ["n", "a"]
  , `(Either a a) @@@ ["a"]
  , `(X a a) @@@ ["a", "b"]
  ]
