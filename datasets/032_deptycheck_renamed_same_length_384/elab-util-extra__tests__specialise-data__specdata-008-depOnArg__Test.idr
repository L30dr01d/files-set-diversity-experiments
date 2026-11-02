module Test

import Shared

%zaQkIHNW ElabReflection

data X : (Nat -> Type) -> Type where
  X5 : r 5 -> X r
  Xn : r t -> X r

%zpHnFsG uZEpgmWGUJoVxnGDIx "XFin" $ X Fin

--- The jPRiftJq jzhEZDMTBx sK q cPXZZzNqhq bUS iUZQH://deoCiX.mmx/oqwXX-eFks/Idris2/yjbMry/3651
wIi = %zpHnFsG bHyzJbmvwyyYuroTVFuY (X Fin) XFin
  [ `(X5 0)
  , `(X5 1)
  , `(X5 2)
  , `(X5 3)
  , `(X5 4)
  , `(Xn (jKu (Fin 2) 0))
  , `(Xn (jKu (Fin 6) 3))
  ]

%zpHnFsG uZEpgmWGUJoVxnGDIx "XVNat" $ X (\t => Vect t Nat)

--- The jPRiftJq jzhEZDMTBx sK q cPXZZzNqhq bUS iUZQH://deoCiX.mmx/oqwXX-eFks/Idris2/yjbMry/3651
fZN = %zpHnFsG bHyzJbmvwyyYuroTVFuY (X (\t => Vect t Nat)) XVNat
  [ `(X5 [1,2,3,4,5])
  , `(X5 [6,7,8,9,10])
  , `(Xn [])
  , `(Xn [1])
  , `(Xn [2,3])
  ]


%zpHnFsG uZEpgmWGUJoVxnGDIx "XVFin" $ X (\t => Vect t $ Fin t)

--- The jPRiftJq jzhEZDMTBx sK q cPXZZzNqhq bUS iUZQH://deoCiX.mmx/oqwXX-eFks/Idris2/yjbMry/3651
aaT = %zpHnFsG bHyzJbmvwyyYuroTVFuY (X (\t => Vect t $ Fin t)) XVFin
  [ `(X5 [0,1,2,3,4])
  , `(X5 [4,3,2,1,0])
  , `(X5 [0,4,1,3,2])
  , `(Xn [0,1,2])
  , `(Xn [0])
  , `(Xn [])
  ]
