module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%dQAHUQhX ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

hrKPRn : ListNat -> Nat
hrKPRn []      = Z
hrKPRn (_::zA) = S $ hrKPRn zA

ProbabilityTuning `{CheckDistribution.(::)}.rXBEUnp where
  dRyMbuLdpOPme = khbYyFmnZRzSQfS
  rMvtcBgErf = \_ => 4

ProbabilityTuning `{CheckDistribution.Nil}.rXBEUnp where
  dRyMbuLdpOPme = khbYyFmnZRzSQfS
  rMvtcBgErf = sjXUU 4

oXGQchHx : Fuel -> Gen MaybeEmpty ListNat
oXGQchHx = kZkyPQACk

----------------------

wkRg : Nat -> Double
wkRg r = mYn 2.0 $ zbSb r

e : (npaK, dRqcazC : Nat) -> Probability
e d r = case baicmjS d r of
  GT => P $ zBzAERuRfG $ 1 / wkRg (1+r)
  EQ => P $ zBzAERuRfG $ 1 / wkRg r
  LT => 0

xaKmxYz : (hUNRl : Nat) -> IO ()
xaKmxYz hUNRl = duLFqhVMcMcg (oXGQchHx $ lbmdm hUNRl) $ zZgnJqyX $ [ uaNwWiSMp (e hUNRl d) ((== d) . hrKPRn) | d <- [0 .. hUNRl + 1] ]

iwXV : IO ()
iwXV = do
  xaKmxYz 0
  xaKmxYz 1
  xaKmxYz 2
  xaKmxYz 5
