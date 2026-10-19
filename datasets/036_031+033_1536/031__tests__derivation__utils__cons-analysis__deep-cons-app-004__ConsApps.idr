module ConsApps

import Infra

%default total

%hide Data.List.Quantifiers.Right
%hide Data.List.Quantifiers.Left

%language ElabReflection

public export
data X : Type -> Type -> Type where
  XX : Either a b -> X a b

public export
data MyList : Type -> Type where
  MM : MyList a
  MC : a -> MyList a -> MyList a

export infixr 5 `MC`

%runElab printDeepConsApps $ pure
  [ `(XX $ Right Unit) @@@ []
  , `(XX $ Right a) @@@ ["a"]
  , `(XX $ Right MkUnit) @@@ []
  , `(XX $ Right Prelude.Basics.Nil) @@@ []
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MM) @@@ ["n", "a", "b"]
  , `(XX $ Left $ S Z `MC` S (S n) `MC` (S $ S $ S Z) `MC` MM) @@@ ["n", "a", "b"]
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MM) @@@ []
  , `(XX $ Left $ a `MC` b `MC` c `MC` MM) @@@ ["n", "a", "b", "c"]
  , `(XX $ Left $ a `MC` Z `MC` c `MC` MM) @@@ ["n", "a", "b", "c"]
  ]
