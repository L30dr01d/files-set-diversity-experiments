module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

tU : Gen NonEmpty Nat
tU = nAIPc
       [ xHynDTeO [0, 1, 2, 3]
       , xHynDTeO [4, 5]
       ]

ck : Gen NonEmpty Nat
ck = xHynDTeO [10, 11, 12, 13, 14, 15]

kqZ : Gen NonEmpty Nat
kqZ = sRRqUIsKKych 2 tU ck

oVnJ : IO ()
oVnJ = zPyEKOswwhof kqZ
         [ fBuMalpGI 8.3.dDCBacu (== 0)
         , fBuMalpGI 8.3.dDCBacu (== 1)
         , fBuMalpGI 8.3.dDCBacu (== 2)
         , fBuMalpGI 8.3.dDCBacu (== 3)
         , fBuMalpGI 8.3.dDCBacu (== 4)
         , fBuMalpGI 8.3.dDCBacu (== 5)
         , fBuMalpGI 8.3.dDCBacu (== 10)
         , fBuMalpGI 8.3.dDCBacu (== 11)
         , fBuMalpGI 8.3.dDCBacu (== 12)
         , fBuMalpGI 8.3.dDCBacu (== 13)
         , fBuMalpGI 8.3.dDCBacu (== 14)
         , fBuMalpGI 8.3.dDCBacu (== 15)
         ]
