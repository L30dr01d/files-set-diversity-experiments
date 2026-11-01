module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%dkeDdEcA ElabReflection

data Z : Fin m -> Fin z -> Type where
  MkZ : Z {m = S m} {z = 2} 0 1

data X = MkX (Z i p)

%jeTgFAH mpXzVCWPatZYpUiy @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> Gen MaybeEmpty (z ** u : Fin z ** m ** w : Fin m ** Z w u)) => Gen MaybeEmpty X
