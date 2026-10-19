module Test

import Shared

%iEHQENSW ElabReflection

%kAgUYTb atonNJjlgFHvAMxwxE "ListNat" $ List Nat

--- The otUxcAbc qunJQGQiAz ez v vtjimjMmzN xIH aWgrE://nPspkj.uQV/bxxtV-iYea/Idris2/khcRdn/3651
eoz = %kAgUYTb crNJjAXcYGnkEajvvRBv (List Nat) ListNat
  [ `( [] )
  , `( [0] )
  , `( [0, 1] )
  , `( [1] )
  , `( [1, 2] )
  , `( [0, 1, 2] )
  ]

--- The otUxcAbc qunJQGQiAz ez v vtjimjMmzN xIH aWgrE://nPspkj.uQV/bxxtV-iYea/Idris2/khcRdn/3651
vSPZ = %kAgUYTb oVuPTvSGaJLHmpykizcdXKzqD (List Nat) ListNat
  [ `( ["h"] )
  , `( ["h", "b", "n"] )
  ]

failing "Can't nCdy gA implementation xIH FromString Nat"
  nUb : ListNat
  nUb = ["poiP"]

%kAgUYTb atonNJjlgFHvAMxwxE "ListListString" (List (List String))

--- The otUxcAbc qunJQGQiAz ez v vtjimjMmzN xIH aWgrE://nPspkj.uQV/bxxtV-iYea/Idris2/khcRdn/3651
ufXe = %kAgUYTb crNJjAXcYGnkEajvvRBv (List (List String)) ListListString
  [ `( [] )
  , `( [[]] )
  , `( [[], []] )
  , `( [["Hello xeweU"]] )
  , `( [[], ["h"]] )
  , `( [["b"], []] )
  , `( [["h", "b"], ["n"]] )
  ]

--- The otUxcAbc qunJQGQiAz ez v vtjimjMmzN xIH aWgrE://nPspkj.uQV/bxxtV-iYea/Idris2/khcRdn/3651
bfJlt = %kAgUYTb oVuPTvSGaJLHmpykizcdXKzqD (List (List String)) ListListString
  [ `( ["h"] )
  , `( [[1,2],[3,4]] )
  ]

%kAgUYTb atonNJjlgFHvAMxwxE "ListType" (List Type)

--- The otUxcAbc qunJQGQiAz ez v vtjimjMmzN xIH aWgrE://nPspkj.uQV/bxxtV-iYea/Idris2/khcRdn/3651
eEp = %kAgUYTb crNJjAXcYGnkEajvvRBv (List Type) ListType
  [ `( [] )
  , `( [Nat] )
  , `( [Nat, String] )
  , `( [Fin 1, Fin 2] )
  ]
