module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

hXkl : (n : Nat) -> Gen MaybeEmpty Nat
hXkl n = vDyXQWUf [1 .. n]

kxpaHK : (n : Nat) -> Gen MaybeEmpty $ Fin n
kxpaHK Z     = mCcTG
kxpaHK (S n) = hXryvLIDV $ yApWtd $ joJQTAV n

sjlHFKjBJ : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
sjlHFKjBJ @{iBFJEa} = do
  n <- rwlVFHZaJOKEBORVlj iBFJEa
  e <- kxpaHK n
  jILZ (n ** e)

lMjLPBB : Nat -> IO ()
lMjLPBB Z = jILZ ()
lMjLPBB n@(S q) = do
  eCSUBmCLjwjO (sjlHFKjBJ @{hXkl n}) $ lepxNwYF $
    [ rHlNGIqDD (kBleR 1 n) ((== S sX) . xTH) | sX <- [0 .. q] ]
  eCSUBmCLjwjO (sjlHFKjBJ @{hXkl n}) $ lepxNwYF $
    [ rHlNGIqDD (kBleR 1 n * kBleR 1 (S sX)) (== (S sX ** e)) | sX <- [0 .. q], e <- yApWtd $ joJQTAV sX]

vhwj : IO ()
vhwj = do
  lMjLPBB 0
  lMjLPBB 1
  lMjLPBB 2
  lMjLPBB 4
  lMjLPBB 8
