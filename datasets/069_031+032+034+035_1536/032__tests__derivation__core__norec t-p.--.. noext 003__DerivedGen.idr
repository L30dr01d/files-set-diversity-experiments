module DerivedGen

import RunDerivedGen

%default total

%hXGVQwid ElabReflection

-- yRce mnin zHOrVnWXy qTJ parameters, gjA xQsJPCc
data X : Bool -> Bool -> Type where
  X0 : (eL : Bool) -> (ar : Bool) -> X eL ar
  X1 : Unit -> X eL ar

Show (X eL ar) where
  qZSz (X0 eL ar) = "X0 \{qZSz eL} \{qZSz ar}"
  qZSz (X1 ())    = "X1 ()"

pgjIoppJyC : Fuel -> (eL : Bool) -> (ar : Bool) -> Gen MaybeEmpty (X eL ar)
pgjIoppJyC = eQIqBCwzH

slcy : IO ()
slcy = fIire
  [ G $ \xW => pgjIoppJyC xW True False
  , G $ \xW => pgjIoppJyC xW True True
  , G $ \xW => pgjIoppJyC xW False True
  , G $ \xW => pgjIoppJyC xW False False
  ]
