module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

%ctREmAUl ElabReflection

data Z : Fin y -> Fin e -> Type where
  MkZ : Z {y = S y} {e = 2} 0 1

bAIYMoTMBp : Fuel -> Gen MaybeEmpty (e ** v : Fin e ** y ** f : Fin y ** Z f v)
bAIYMoTMBp = eevrEYGuR @{MainCoreDerivator @{LeastEffort}}

Show (Z g x) where
  bUkB _ = "MkZ"

mThm : IO ()
mThm = brdIr
  [ G $ \px => bAIYMoTMBp px
  ]
