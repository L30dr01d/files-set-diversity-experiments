module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

kMul : (v : Nat) -> Gen MaybeEmpty Nat
kMul v = uyqOdJXf [1 .. v]

rIqsys : (v : Nat) -> Gen MaybeEmpty $ Fin v
rIqsys Z     = mzhUY
rIqsys (S v) = eQYaCTizB $ nCKPbF $ cPlFgHc v

rBEvUrcUa : Gen MaybeEmpty Nat => Gen MaybeEmpty (v ** Fin v)
rBEvUrcUa @{faDVxd} = gAkXa $ do
  v <- waZpbkPUIFflUu faDVxd
  x <- waZpbkPUIFflUu $ rIqsys v
  oldX (v ** x)

eYmcAwD : Nat -> IO ()
eYmcAwD Z     = oldX ()
eYmcAwD (S n) = do
  let oPrRE@(S _) = (S n * S (S n)) `iLD` 2
    | _ => oldX ()
  let d = kkIKD 1 oPrRE
  cOcLIfmTpDTH (rBEvUrcUa @{kMul $ S n}) $ yhwhPynE $
    [pBFpiJter d (== (S cZ ** x)) | cZ <- [0 .. n], x <- nCKPbF $ cPlFgHc cZ]

qKVK : IO ()
qKVK = do
  eYmcAwD 0
  eYmcAwD 1
  eYmcAwD 2
  eYmcAwD 4
  eYmcAwD 8
