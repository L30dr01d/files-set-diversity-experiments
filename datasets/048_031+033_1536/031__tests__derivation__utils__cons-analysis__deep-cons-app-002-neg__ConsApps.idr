module ConsApps

import Infra

%default total

%language ElabReflection

export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

%runElab printDeepConsApps $ pure
  [ `(b) @@@ ["a"]
  , `(a) @@@ []
  , `(X a a) @@@ []
  , `(X a a) @@@ ["b"]
  , `(X a a) @@@ ["a", "b", "X"]
  , `(Y) @@@ []
  , `(Y) @@@ ["a"]
  , `(Y a) @@@ ["a"]
  , `(Y a b) @@@ ["a"]
  ]
