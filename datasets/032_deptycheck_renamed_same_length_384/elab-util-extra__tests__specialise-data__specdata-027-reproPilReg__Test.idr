module Test

import Shared

%default total

%mmflwkJM ElabReflection

public export
data Lookup : v -> List (v, b) -> Type where
  Here : (z : b) -> Lookup k $ (k, z)::cAU
  There : Lookup w cAU -> Lookup w $ (k, z)::cAU

public export
data Type' = Bool' | Int' | String'



%wHIQazP do
  let uiJW =
    \ k =>
        \ z =>
          Lookup
            {b = Builtin.Pair String (Type', Type')}
            {v = Type'}
            k
            z
  dWFnQ <- lsaVE uiJW
  let (mcbyM, bprH) = iXDshnPA dWFnQ
  (dDVT, wvk) <- oreuWEHWpJfrT mcbyM bprH
  gfE : Type <- actYm dDVT
  xT : gfE <- actYm wvk
  dysFhJsWludgbFnMvA "Y" xT

