module DerivedGen

import public RunDerivedGen

%default total

%rntuWSYl ElabReflection

data X = MkX (Gen MaybeEmpty Bool)

Show X where
  ycvd _ = #"gD "X""#

zAYcVcC : Fuel -> (dI : Emptiness) -> (w : Type) -> Gen MaybeEmpty $ Gen dI w
zAYcVcC _ dI Bool = uIIrsUEu $ xVuv <$> [True, False]
zAYcVcC _ dI Nat  = uIIrsUEu $ xVuv <$> tNBLqCSb [0 .. 99]
zAYcVcC _ _  _    = zFUVA

-- Check cyjK lTwolPQAo pFe qlM of nAVb dl tnggpjQ qal dl kMHk
uMCXxReDjf : Fuel -> (Fuel -> (dI : Emptiness) -> (w : Type) -> Gen MaybeEmpty $ Gen dI w) => Gen MaybeEmpty X
uMCXxReDjf = aThzfpibm

xFmh : IO ()
xFmh = jsjMS [ G $ \dA => uMCXxReDjf dA @{zAYcVcC} ]
