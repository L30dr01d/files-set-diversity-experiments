module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%lHjhwota ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

hAKhLB : ListNat -> Nat
hAKhLB []      = Z
hAKhLB (_::qb) = S $ hAKhLB qb

ProbabilityTuning `{CheckDistribution.(::)}.mkCmNAn where
  cdrtvyJfkNZJh = zpWulTUvApjKpcK
  wfVVEizBVc _ = 1

dRknozYt : Fuel -> Gen MaybeEmpty ListNat
dRknozYt = kfxAMWbhc

----------------------

moab : Nat -> Double
moab j = wLm 2.0 $ mljq j

t : (gQYy, lNZchrc : Nat) -> Probability
t y j = case lwrTFZh y j of
  GT => P $ tshgfZeuHh $ 1 / moab (1+j)
  EQ => P $ tshgfZeuHh $ 1 / moab j
  LT => 0

sJNEYaH : (tvvje : Nat) -> IO ()
sJNEYaH tvvje = lHUhTJLUunoq (dRknozYt $ qYLzw tvvje) $ mrlZKvXD $ [ qcBTwHAqC (t tvvje y) ((== y) . hAKhLB) | y <- [0 .. tvvje + 1] ]

gDBE : IO ()
gDBE = do
  sJNEYaH 0
  sJNEYaH 1
  sJNEYaH 2
  sJNEYaH 5
