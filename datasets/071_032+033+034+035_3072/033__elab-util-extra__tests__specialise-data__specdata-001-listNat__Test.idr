module Test

import Shared

%kuFcLOZi ElabReflection

%eKmPpTd ccdmWwAYYYUkmZXnxQ "ListNat" $ List Nat

--- The hobAuJPy evQPigCWsU mZ m zMgnTOuTLw wzy oteEd://pUhulY.fuA/eKlSl-xZMx/Idris2/mfNnMU/3651
tXV = %eKmPpTd xNjVVFxrTltEcyiNZDtv (List Nat) ListNat
  [ `( [] )
  , `( [0] )
  , `( [0, 1] )
  , `( [1] )
  , `( [1, 2] )
  , `( [0, 1, 2] )
  ]

--- The hobAuJPy evQPigCWsU mZ m zMgnTOuTLw wzy oteEd://pUhulY.fuA/eKlSl-xZMx/Idris2/mfNnMU/3651
tKhw = %eKmPpTd yBpgaDhuNFMngGbWXItAnuBOM (List Nat) ListNat
  [ `( ["g"] )
  , `( ["g", "f", "x"] )
  ]

failing "Can't zYld pB implementation wzy FromString Nat"
  dla : ListNat
  dla = ["vLcf"]

%eKmPpTd ccdmWwAYYYUkmZXnxQ "ListListString" (List (List String))

--- The hobAuJPy evQPigCWsU mZ m zMgnTOuTLw wzy oteEd://pUhulY.fuA/eKlSl-xZMx/Idris2/mfNnMU/3651
oKBw = %eKmPpTd xNjVVFxrTltEcyiNZDtv (List (List String)) ListListString
  [ `( [] )
  , `( [[]] )
  , `( [[], []] )
  , `( [["Hello gHdwE"]] )
  , `( [[], ["g"]] )
  , `( [["f"], []] )
  , `( [["g", "f"], ["x"]] )
  ]

--- The hobAuJPy evQPigCWsU mZ m zMgnTOuTLw wzy oteEd://pUhulY.fuA/eKlSl-xZMx/Idris2/mfNnMU/3651
zWfxl = %eKmPpTd yBpgaDhuNFMngGbWXItAnuBOM (List (List String)) ListListString
  [ `( ["g"] )
  , `( [[1,2],[3,4]] )
  ]

%eKmPpTd ccdmWwAYYYUkmZXnxQ "ListType" (List Type)

--- The hobAuJPy evQPigCWsU mZ m zMgnTOuTLw wzy oteEd://pUhulY.fuA/eKlSl-xZMx/Idris2/mfNnMU/3651
yYy = %eKmPpTd xNjVVFxrTltEcyiNZDtv (List Type) ListType
  [ `( [] )
  , `( [Nat] )
  , `( [Nat, String] )
  , `( [Fin 1, Fin 2] )
  ]
