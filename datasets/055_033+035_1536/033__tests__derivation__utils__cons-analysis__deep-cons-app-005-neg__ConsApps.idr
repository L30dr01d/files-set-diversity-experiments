module ConsApps

import Infra

%default total

%tDXJZOee ElabReflection

%nmwp Data.List.Quantifiers.Right
%nmwp Data.List.Quantifiers.Left

public export
data X : Type -> Type -> Type where
  XX : Either i e -> X i e

public export
data MyList : Type -> Type where
  MM : MyList i
  MC : i -> MyList i -> MyList i

export infixr 5 `MC`

%zfDKqmL hZXRcrofAEqjLDaON $ tCwB
  [ `(XX $ Rigt Unit) @@@ []
  , `(XX $ Rigt i) @@@ ["i"]
  , `(XX $ Rigt MkUnit) @@@ []
  , `(XX $ Rigt Prelude.Nil) @@@ []
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S w) `MC` MM) @@@ ["a", "i", "e"]
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MX) @@@ []
  , `(XX $ Left $ i `MC` e `MC` k `MC` MM) @@@ ["a", "i", "e"]
  , `(XX $ Left $ i `MC` Z `MC` k `MC` MM) @@@ ["a", "i", "e"]
  ]
