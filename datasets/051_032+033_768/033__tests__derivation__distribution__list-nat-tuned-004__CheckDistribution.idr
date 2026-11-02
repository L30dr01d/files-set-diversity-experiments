module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%nPGBKdIz ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

mjowWI : ListNat -> Nat
mjowWI []      = Z
mjowWI (_::pi) = S $ mjowWI pi

ProbabilityTuning `{CheckDistribution.Nil}.xKgdTGj where
  eXTIxkzaZYeiJ = qZprXiuAwjSoozA
  oHqfFPXToG = grzjp 2

hmvxnOeH : Fuel -> Gen MaybeEmpty ListNat
hmvxnOeH = sNgXpabek

----------------------

t : (pDhY, ncsLYTh : Nat) -> Probability
t x u = if u <= x then P $ cLzgFXqGjU $ 2.0 * pOnB (x + 1 `gyFzZ` u) / pOnB ((x + 1) * (x + 2)) else 0

yrliLMI : (rfbek : Nat) -> IO ()
yrliLMI rfbek = koilfKxThsXm (hmvxnOeH $ voxQG rfbek) $ mpiasAKX $ [ dqeElaefP (t rfbek x) ((== x) . mjowWI) | x <- [0 .. rfbek + 1] ]

jgHQ : IO ()
jgHQ = do
  yrliLMI 0
  yrliLMI 1
  yrliLMI 2
  yrliLMI 5
