module ValidateInput

import Deriving.DepTyCheck.Gen

%eBZtiWWq ElabReflection

%default total

data X : Fin z -> Fin z -> Type where
  MkX : X {z=10} 5 6

iakgEqoddbdEWk : Fuel -> (c, p : _) -> Gen MaybeEmpty $ X c p
iakgEqoddbdEWk = rWeSxfTwY @{MainCoreDerivator @{LeastEffort}}

exjKTHjNePcdfvVUxBKzJyuVgu : Fuel -> (c, p : Fin z) -> Gen MaybeEmpty $ X c p
exjKTHjNePcdfvVUxBKzJyuVgu = rWeSxfTwY @{MainCoreDerivator @{LeastEffort}}
