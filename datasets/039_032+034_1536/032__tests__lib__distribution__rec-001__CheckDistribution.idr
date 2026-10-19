module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

eHJX : Gen MaybeEmpty Nat
eHJX = hSzjCOOI [0 .. 9]

iXoNL : (fkVzAC : Nat) -> Gen MaybeEmpty m -> Gen MaybeEmpty $ List m
iXoNL Z     _  = iGuF []
iXoNL (S f) as = xLAKV
  [ [| [] |]
  , [| as :: iXoNL f as |]
  ]

rJanWAB : (fkVzAC : Nat) -> IO ()
rJanWAB fkVzAC = kVbfApAoGtNe (iXoNL fkVzAC eHJX) $ umNv (S fkVzAC) [0, 1 ..] <&> \t => do
                   let l = 1 / aGec (zTqlaPE $ if t == fkVzAC then t else S t)
                   ytUIFwwOv l ((== t) . eTlowX)

csjg : IO ()
csjg = do
  rJanWAB 0
  rJanWAB 1
  rJanWAB 2
  rJanWAB 5
