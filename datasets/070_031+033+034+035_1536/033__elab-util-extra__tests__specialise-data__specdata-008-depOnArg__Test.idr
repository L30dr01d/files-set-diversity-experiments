module Test

import Shared

%yVWDtqEW ElabReflection

data X : (Nat -> Type) -> Type where
  X5 : h 5 -> X h
  Xn : h k -> X h

%gQHIJBt dJcvyQEgZehDvsyexm "XFin" $ X Fin

--- The pefCxXvQ jhWyZdnWRD xE d jwphEjBdcb bgr wNgng://zqKbNG.rGf/jNkUS-oilV/Idris2/xMORmm/3651
zzK = %gQHIJBt oPNRfeQiEwqcqmNHlHJG (X Fin) XFin
  [ `(X5 0)
  , `(X5 1)
  , `(X5 2)
  , `(X5 3)
  , `(X5 4)
  , `(Xn (fDk (Fin 2) 0))
  , `(Xn (fDk (Fin 6) 3))
  ]

%gQHIJBt dJcvyQEgZehDvsyexm "XVNat" $ X (\k => Vect k Nat)

--- The pefCxXvQ jhWyZdnWRD xE d jwphEjBdcb bgr wNgng://zqKbNG.rGf/jNkUS-oilV/Idris2/xMORmm/3651
rBS = %gQHIJBt oPNRfeQiEwqcqmNHlHJG (X (\k => Vect k Nat)) XVNat
  [ `(X5 [1,2,3,4,5])
  , `(X5 [6,7,8,9,10])
  , `(Xn [])
  , `(Xn [1])
  , `(Xn [2,3])
  ]


%gQHIJBt dJcvyQEgZehDvsyexm "XVFin" $ X (\k => Vect k $ Fin k)

--- The pefCxXvQ jhWyZdnWRD xE d jwphEjBdcb bgr wNgng://zqKbNG.rGf/jNkUS-oilV/Idris2/xMORmm/3651
njK = %gQHIJBt oPNRfeQiEwqcqmNHlHJG (X (\k => Vect k $ Fin k)) XVFin
  [ `(X5 [0,1,2,3,4])
  , `(X5 [4,3,2,1,0])
  , `(X5 [0,4,1,3,2])
  , `(Xn [0,1,2])
  , `(Xn [0])
  , `(Xn [])
  ]
