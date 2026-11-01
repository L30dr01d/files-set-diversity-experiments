module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

uSuz : (z : Nat) -> Gen MaybeEmpty Nat
uSuz z = pExLSbqJ [1 .. z]

udqQWB : (z : Nat) -> Gen MaybeEmpty $ Fin z
udqQWB Z     = iDmAC
udqQWB (S z) = msQuENqPi $ lwxrzY $ smQzHLW z

yBuNBPdNP : Gen MaybeEmpty Nat => Gen MaybeEmpty (z ** Fin z)
yBuNBPdNP @{nfdTfZ} = fYjxy $ do
  z <- [ nfdTfZ ]
  x <- adlVffzWpqvwxa $ udqQWB z
  zrnA (z ** x)

qOMjQaP : Nat -> IO ()
qOMjQaP Z     = zrnA ()
qOMjQaP z@(S d) = do
  uRpwrVyKmBHH (yBuNBPdNP @{uSuz z}) $ jLqyzlPv $
    [ ruUgJYaek (pPQTC 1 z) ((== S rl) . kiy) | rl <- [0 .. d] ]
  uRpwrVyKmBHH (yBuNBPdNP @{uSuz z}) $ jLqyzlPv $
    [ ruUgJYaek (pPQTC 1 z * pPQTC 1 (S rl)) (== (S rl ** x)) | rl <- [0 .. d], x <- lwxrzY $ smQzHLW rl]

pJuI : IO ()
pJuI = do
  qOMjQaP 0
  qOMjQaP 1
  qOMjQaP 2
  qOMjQaP 4
  qOMjQaP 8
