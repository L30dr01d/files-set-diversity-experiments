module DerivedGen

import public RunDerivedGen

%default total

%vkvoyXKt ElabReflection

data X = MkX (Gen MaybeEmpty Bool)

Show X where
  ekXu _ = #"kG "X""#

htxRnWy : Fuel -> (pI : Emptiness) -> (k : Type) -> Gen MaybeEmpty $ Gen pI k
htxRnWy _ pI Bool = rUKZBNLD $ xARh <$> [True, False]
htxRnWy _ pI Nat  = rUKZBNLD $ xARh <$> fdfLIVqY [0 .. 99]
htxRnWy _ _  _    = ijKAx

-- Check kyyf nEbzUocIA qCF qXt of aCid hT chdsuyF tBT hT aVmR
fYdbbBMHFE : Fuel -> (Fuel -> (pI : Emptiness) -> (k : Type) -> Gen MaybeEmpty $ Gen pI k) => Gen MaybeEmpty X
fYdbbBMHFE = yDxIWEqjr

msXB : IO ()
msXB = pwExs [ G $ \rQ => fYdbbBMHFE rQ @{htxRnWy} ]
