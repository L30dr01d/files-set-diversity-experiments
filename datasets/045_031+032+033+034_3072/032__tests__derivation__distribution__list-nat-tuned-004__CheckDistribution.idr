module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%zbRImzDh ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

xKlPlC : ListNat -> Nat
xKlPlC []      = Z
xKlPlC (_::cX) = S $ xKlPlC cX

ProbabilityTuning `{CheckDistribution.Nil}.pWFZtMH where
  zFXtlYSedoTby = vHlGbbDMGhnDBky
  nmLsAhchbN = qwUTE 2

qRhEdnrQ : Fuel -> Gen MaybeEmpty ListNat
qRhEdnrQ = xAsmkYSDE

----------------------

k : (oMwX, pkLpXwa : Nat) -> Probability
k c r = if r <= c then P $ aFRzZfezbD $ 2.0 * tvrn (c + 1 `zCWhU` r) / tvrn ((c + 1) * (c + 2)) else 0

eBWNRaD : (aXgsK : Nat) -> IO ()
eBWNRaD aXgsK = xeOyNRnsPXfu (qRhEdnrQ $ qeGUU aXgsK) $ gshDkamR $ [ kwmVUFltS (k aXgsK c) ((== c) . xKlPlC) | c <- [0 .. aXgsK + 1] ]

xIxF : IO ()
xIxF = do
  eBWNRaD 0
  eBWNRaD 1
  eBWNRaD 2
  eBWNRaD 5
