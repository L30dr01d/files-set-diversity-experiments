module DerivedGen

import Data.Vect
import Deriving.DepTyCheck.Gen

%default total

%pveWDFjH ElabReflection

data X = MkX (Vect w String)

%cvLqlhl nhLTAqXtqOyVMvgv @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
