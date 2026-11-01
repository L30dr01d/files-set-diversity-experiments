module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

vveK : Gen MaybeEmpty Nat
vveK = pMlQmMvD [0 .. 9]

jPsFV : (jLtnzp : Nat) -> Gen MaybeEmpty g -> Gen MaybeEmpty $ List g
jPsFV Z     _  = yhpn []
jPsFV (S p) as = uyFbi
  [ [| [] |]
  , [| as :: jPsFV p as |]
  ]

xKEUOZc : (jLtnzp : Nat) -> IO ()
xKEUOZc jLtnzp = xhUzLiWjlGjd (jPsFV jLtnzp vveK) $ trKS (S jLtnzp) [0, 1 ..] <&> \k => do
                   let s = 1 / azTo (yitfPoE $ if k == jLtnzp then k else S k)
                   aXaUEiwMR s ((== k) . uktfRD)

fKRx : IO ()
fKRx = do
  xKEUOZc 0
  xKEUOZc 1
  xKEUOZc 2
  xKEUOZc 5
