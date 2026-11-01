module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

uNIf : Gen MaybeEmpty Nat
uNIf = eSFRrSTi [0 .. 9]

umvCp : (rUCXnF : Nat) -> Gen MaybeEmpty h -> Gen MaybeEmpty $ List h
umvCp Z     _  = eSHX []
umvCp (S e) as = omBSHMoxs
  [ (1, [| [] |])
  , (3, [| as :: umvCp e as |])
  ]

mREdR : Probability
mREdR = 1/4

rrx : Probability
rrx = 3/4

gKrK : Nat -> Probability
gKrK 0 = 1
gKrK 1 = rrx
gKrK (S e) = rrx * gKrK e

aIsyXXf : (rUCXnF : Nat) -> IO ()
aIsyXXf rUCXnF = aUOcpJfSawaE (umvCp rUCXnF uNIf) $ bOVj rUCXnF [0, 1 ..] <&> \x => do
                   let i = gKrK x * mREdR
                   dINCsRWGI i ((== x) . meMFLv)

exqk : IO ()
exqk = do
  aIsyXXf 0
  aIsyXXf 1
  aIsyXXf 2
  aIsyXXf 5
  aIsyXXf 10
