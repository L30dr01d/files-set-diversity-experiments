module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

cXrf : (n : Nat) -> Gen MaybeEmpty Nat
cXrf n = aRyGEDDo [1 .. n]

ecmSLF : (n : Nat) -> Gen MaybeEmpty $ Fin n
ecmSLF Z     = aEWnv
ecmSLF (S n) = rjUJAdCfg $ paYQXa $ rgJetYr n

oHanBXIQh : Gen MaybeEmpty Nat => Gen MaybeEmpty (n ** Fin n)
oHanBXIQh @{mAADVO} = do
  n <- mAADVO
  i <- ecmSLF n
  kqeg (n ** i)

ztLDrVO : Nat -> IO ()
ztLDrVO Z = kqeg ()
ztLDrVO n@(S w) = do
  oiyhrqNErpFn (oHanBXIQh @{cXrf n}) $ efmzawWq $
    [ ejKVfvzAv (vWgyd 1 n) ((== S yh) . oEL) | yh <- [0 .. w] ]
  oiyhrqNErpFn (oHanBXIQh @{cXrf n}) $ efmzawWq $
    [ ejKVfvzAv (vWgyd 1 n * vWgyd 1 (S yh)) (== (S yh ** i)) | yh <- [0 .. w], i <- paYQXa $ rgJetYr yh]

xdle : IO ()
xdle = do
  ztLDrVO 0
  ztLDrVO 1
  ztLDrVO 2
  ztLDrVO 4
  ztLDrVO 8
