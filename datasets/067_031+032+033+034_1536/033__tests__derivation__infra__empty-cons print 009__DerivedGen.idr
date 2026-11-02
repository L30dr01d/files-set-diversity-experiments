module DerivedGen

import AlternativeCore

import Deriving.DepTyCheck.Gen

import Data.Vect

%default total

%awkZJwFM ElabReflection

data Y = Y0 | Y1

data X = X0 | X1 | X2 Y

%vphquBu appNBrevbRitkDkX @{EmptyCons} $ Fuel -> Gen MaybeEmpty X
