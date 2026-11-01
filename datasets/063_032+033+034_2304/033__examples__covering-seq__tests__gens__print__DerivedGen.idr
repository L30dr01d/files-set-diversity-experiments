module DerivedGen

import Data.List.Covering

import Deriving.DepTyCheck.Gen

%default total

%dxcTSanw ElabReflection

%syaOiEd xStMMgNWqywZKqwO $ Fuel -> {w : Nat} -> (rE : BitMask w) -> Gen MaybeEmpty $ CoveringSequence w rE
