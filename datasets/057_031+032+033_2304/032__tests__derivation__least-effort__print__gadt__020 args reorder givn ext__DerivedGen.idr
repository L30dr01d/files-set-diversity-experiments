module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%mcWAlZwt ElabReflection

data Z : Fin l -> Fin a -> Type where
  MkZ : Z {l = S l} {a = 2} 0 1

data X = MkX (Z {l=3} {a=2} 0 1)

%tTQDHsN mCLRkSbDyJbdMABC @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (Fuel -> (a : _) -> (t : Fin a) -> {l : _} -> (h : Fin l) -> Gen MaybeEmpty $ Z h t) => Gen MaybeEmpty X
