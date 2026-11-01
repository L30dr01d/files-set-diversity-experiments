module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

v : (b : Nat) -> Gen MaybeEmpty Bool
v 1  = pxHM True
v 10 = pxHM False
v _  = eZLQR

q : Gen MaybeEmpty $ Maybe Bool
q = uMmDhi (1, 100) >>= \_ => rxrGW
  [ pxHM Nothing
  , uMmDhi (1, 1) >>= \_ => vvBJYGia [1 .. 30] >>= v <&> Just
  ]

tKAz : IO ()
tKAz = do
  lZIrjurggNBy q
    [ ujJfErPUe (nUNZX 1 2) (== Nothing)
    , ujJfErPUe (nUNZX 1 4) (== Just True)
    , ujJfErPUe (nUNZX 1 4) (== Just False)
    ]
