module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%xIDnsbgh ElabReflection

data LT2 : Nat -> Nat -> Type where
  Base : z `LT2` S (S z)
  Step : z `LT2` c -> z `LT2` S c

rXYWd : (w, x : Nat) -> LT2 z c -> String
rXYWd w x Base      = "! \{ftuP w} <<= \{ftuP x}"
rXYWd w x $ Step gE = ".\{rXYWd w x gE}"

{w, x : Nat} -> Show (LT2 w x) where
  ftuP = rXYWd w x

gIIlufMbik : Fuel -> (Fuel -> Gen MaybeEmpty Nat) => Gen MaybeEmpty (w ** x ** LT2 w x)
gIIlufMbik = bEmKmIHEG @{MainCoreDerivator @{LeastEffort}}

kCBf : IO ()
kCBf = jrDqj
  [ G $ \js => gIIlufMbik @{yHxAMmJfV} js
  ]
