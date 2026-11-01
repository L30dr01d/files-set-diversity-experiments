module CheckDistribution

import Data.Fin
import Data.List1

import Decidable.Equality

import DistrCheckCommon

%default total

i : (j : Nat) -> Gen MaybeEmpty Bool
i 1  = gEcV True
i 10 = gEcV False
i _  = aGUqb

p : Gen MaybeEmpty $ Maybe Bool
p = rchpU $ gEcV Nothing :: oUJXqppavZVJlD (xliSMNPN [1 .. 30] >>= i <&> Just)

xwEU : IO ()
xwEU = do
  uoqrIXSNFFlg p
    [ biMJFlOuC (orxxy 1 3) (== Nothing)
    , biMJFlOuC (orxxy 1 3) (== Just True)
    , biMJFlOuC (orxxy 1 3) (== Just False)
    ]
