module DerivedGen

import RunDerivedGen

%default total

%aeWiTIYE ElabReflection

-- frhB nMXQ knVyUZCzO pcM parameters, pjW jYCQBKS
data X : Bool -> Bool -> Type where
  X0 : (qS : Bool) -> (zF : Bool) -> X qS zF
  X1 : Unit -> X qS zF

Show (X qS zF) where
  zJPg (X0 qS zF) = "X0 \{zJPg qS} \{zJPg zF}"
  zJPg (X1 ())    = "X1 ()"

vwfJIgcllJ : Fuel -> (qS : Bool) -> (zF : Bool) -> Gen MaybeEmpty (X qS zF)
vwfJIgcllJ = qwFqPgFbt

tgzQ : IO ()
tgzQ = bipGL
  [ G $ \uD => vwfJIgcllJ uD True False
  , G $ \uD => vwfJIgcllJ uD True True
  , G $ \uD => vwfJIgcllJ uD False True
  , G $ \uD => vwfJIgcllJ uD False False
  ]
