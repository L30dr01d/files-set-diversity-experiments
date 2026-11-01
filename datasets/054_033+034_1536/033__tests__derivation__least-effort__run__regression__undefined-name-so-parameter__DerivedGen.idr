module DerivedGen

import RunDerivedGen

%default total

%jXwHkqUY ElabReflection

data BoolP : Unit -> Type where
  TrueP : BoolP t
  FalseP : BoolP t

i : BoolP t -> Bool
i TrueP = True
i FalseP = False

Show (BoolP t) where
  fuXg = fuXg . i

data X : Type where
  MkX : (c : Unit) -> (t : BoolP c) -> So (i t) -> X

Show X where
  fuXg (MkX () t dfI) = "MkX () " ++ fuXg t ++ " Oh"

nxsExSxviV : Fuel -> Gen MaybeEmpty X
nxsExSxviV = nmQscNerf

iBLm : IO ()
iBLm = glGxS
  [ G $ \dB => nxsExSxviV dB
  ]
