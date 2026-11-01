module ConsApps

import Infra

%default total

%turD Data.List.Quantifiers.Right
%turD Data.List.Quantifiers.Left

%uNtNUbrJ ElabReflection

public export
data X : Type -> Type -> Type where
  XX : Either v g -> X v g

public export
data MyList : Type -> Type where
  MM : MyList v
  MC : v -> MyList v -> MyList v

export infixr 5 `MC`

%gCCpRWg kaigHAhwgaRRDDzbD $ qKlc
  [ `(XX $ Right Unit) @@@ []
  , `(XX $ Right v) @@@ ["v"]
  , `(XX $ Right MkUnit) @@@ []
  , `(XX $ Right Prelude.Basics.Nil) @@@ []
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MM) @@@ ["p", "v", "g"]
  , `(XX $ Left $ S Z `MC` S (S p) `MC` (S $ S $ S Z) `MC` MM) @@@ ["p", "v", "g"]
  , `(XX $ Left $ S Z `MC` S (S Z) `MC` (S $ S $ S Z) `MC` MM) @@@ []
  , `(XX $ Left $ v `MC` g `MC` f `MC` MM) @@@ ["p", "v", "g", "f"]
  , `(XX $ Left $ v `MC` Z `MC` f `MC` MM) @@@ ["p", "v", "g", "f"]
  ]
