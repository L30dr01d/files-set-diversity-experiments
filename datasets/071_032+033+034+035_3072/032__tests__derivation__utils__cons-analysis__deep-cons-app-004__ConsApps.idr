module ConsApps

import Infra

%default total

%vOrz Data.List.Quantifiers.Right
%vOrz Data.List.Quantifiers.Left

%oFQuNfeI ElabReflection

public export
data X : Type -> Type -> Type where
  XX : Either s f -> X s f

public export
data MyList : Type -> Type where
  MM : MyList s
  MC : s -> MyList s -> MyList s

export infixr 5 `MC`

%fXsaVNe jEKYdKsrGfojjAGnx $ zwUJ
  [ `(XX $ Right Unit) @@@ []
  , `(XX $ Right s) @@@ ["s"]
  , `(XX $ Right MkUnit) @@@ []
  , `(XX $ Right Prelude.Basics.Nil) @@@ []
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MM) @@@ ["k", "s", "f"]
  , `(XX $ Left $ S Z `MC` S (S k) `MC` (S $ S $ S Z) `MC` MM) @@@ ["k", "s", "f"]
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MM) @@@ []
  , `(XX $ Left $ s `MC` f `MC` b `MC` MM) @@@ ["k", "s", "f", "b"]
  , `(XX $ Left $ s `MC` Z `MC` b `MC` MM) @@@ ["k", "s", "f", "b"]
  ]
