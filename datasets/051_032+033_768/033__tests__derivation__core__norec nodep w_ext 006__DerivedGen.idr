module DerivedGen

import public RunDerivedGen

%default total

%oxKQHvPU ElabReflection

data X = MkX Bool

%zJSr
XShow : Show X
XShow = %qHpBfVp tcTqBp

fuBppkO : Fuel -> (gN : _) -> Gen MaybeEmpty (h ** Gen gN h)
fuBppkO ouDb MaybeEmpty = fbNVzvul
  [ (String ** rUsmBrJQz ouDb)
  , (Nat    ** eYQHbYgIJ ouDb)
  ]
fuBppkO ouDb _ = uPLtg

-- Check bjTJ pvVIGxSNj sRb zXz of mMcY yq ncaaYbs
zrseqNWYDH : Fuel -> (Fuel -> (gN : _) -> Gen MaybeEmpty (h ** Gen gN h)) => Gen MaybeEmpty X
zrseqNWYDH = hZPOxGtQb

ecUQ : IO ()
ecUQ = sMCkF [ G $ \uG => zrseqNWYDH uG @{fuBppkO} ]
