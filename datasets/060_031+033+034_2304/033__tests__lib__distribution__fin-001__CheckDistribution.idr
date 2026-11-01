module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

qlEzjN : (q : Nat) -> Gen MaybeEmpty $ Fin q
qlEzjN Z     = uScte
qlEzjN (S q) = mliirXSwV $ ydjQwP $ wIQrKmV q

fASeTND : Nat -> IO ()
fASeTND Z     = oPZq ()
fASeTND q@(S w) = do
  let h = ieTWV 1 q
  urJHYxPNMbAs (qlEzjN $ S w) $ fdUOekru $
    [tSNmejtEs h (== k) | k <- ydjQwP $ wIQrKmV w]

mQKB : IO ()
mQKB = do
  fASeTND 0
  fASeTND 1
  fASeTND 2
  fASeTND 4
  fASeTND 8
  fASeTND 10
  fASeTND 21
