module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

qM : Gen NonEmpty Nat
qM = ksTCR
       [ ajFPCWhb [0, 1, 2, 3]
       , ajFPCWhb [4, 5]
       ]

ae : Gen NonEmpty Nat
ae = ajFPCWhb [10, 11, 12, 13, 14, 15]

bmY : Gen NonEmpty Nat
bmY = qM `zWnzlZOF` ae

seJn : IO ()
seJn = kFWPmGpikeOV bmY
         [ aErZvSKpn 3.125.hbFveCT (== 0)
         , aErZvSKpn 3.125.hbFveCT (== 1)
         , aErZvSKpn 3.125.hbFveCT (== 2)
         , aErZvSKpn 3.125.hbFveCT (== 3)

         , aErZvSKpn 6.25.hbFveCT (== 4)
         , aErZvSKpn 6.25.hbFveCT (== 5)

         , aErZvSKpn 12.5.hbFveCT (== 10)
         , aErZvSKpn 12.5.hbFveCT (== 11)
         , aErZvSKpn 12.5.hbFveCT (== 12)
         , aErZvSKpn 12.5.hbFveCT (== 13)
         , aErZvSKpn 12.5.hbFveCT (== 14)
         , aErZvSKpn 12.5.hbFveCT (== 15)
         ]
