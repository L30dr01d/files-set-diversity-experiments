module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

hKKI : Gen MaybeEmpty Nat
hKKI = awjcnxrc [0 .. 9]

sonhZ : (qKLryE : Nat) -> Gen MaybeEmpty q -> Gen MaybeEmpty $ List q
sonhZ Z     _  = oPGc []
sonhZ (S i) as = hhjLRgKwb
  [ (1, [| [] |])
  , (3, [| as :: sonhZ i as |])
  ]

aCmXn : Probability
aCmXn = 1/4

tdi : Probability
tdi = 3/4

wwJC : Nat -> Probability
wwJC 0 = 1
wwJC 1 = tdi
wwJC (S i) = tdi * wwJC i

nTYepcJ : (qKLryE : Nat) -> IO ()
nTYepcJ qKLryE = okxtXrNCpdst (sonhZ qKLryE hKKI) $ ajpM qKLryE [0, 1 ..] <&> \r => do
                   let l = wwJC r * aCmXn
                   fYLzvFwXA l ((== r) . pYwFmY)

yVnx : IO ()
yVnx = do
  nTYepcJ 0
  nTYepcJ 1
  nTYepcJ 2
  nTYepcJ 5
  nTYepcJ 10
