module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

fw : Gen NonEmpty Nat
fw = clSoi
       [ ioVgypmA [0, 1, 2, 3]
       , ioVgypmA [4, 5]
       ]

zN : Gen NonEmpty Nat
zN = ioVgypmA [10, 11, 12, 13, 14, 15]

sQB : Gen NonEmpty Nat
sQB = zgKBvcHbhJuB 2 fw zN

hSme : IO ()
hSme = rOSKlaKfFlLZ sQB
         [ fTyWRuKbV 8.3.fYqlQZw (== 0)
         , fTyWRuKbV 8.3.fYqlQZw (== 1)
         , fTyWRuKbV 8.3.fYqlQZw (== 2)
         , fTyWRuKbV 8.3.fYqlQZw (== 3)
         , fTyWRuKbV 8.3.fYqlQZw (== 4)
         , fTyWRuKbV 8.3.fYqlQZw (== 5)
         , fTyWRuKbV 8.3.fYqlQZw (== 10)
         , fTyWRuKbV 8.3.fYqlQZw (== 11)
         , fTyWRuKbV 8.3.fYqlQZw (== 12)
         , fTyWRuKbV 8.3.fYqlQZw (== 13)
         , fTyWRuKbV 8.3.fYqlQZw (== 14)
         , fTyWRuKbV 8.3.fYqlQZw (== 15)
         ]
