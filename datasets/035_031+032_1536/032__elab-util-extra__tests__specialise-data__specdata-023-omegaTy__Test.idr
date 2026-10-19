module Test

import Shared

%esWNEVaY ElabReflection

data X : Type -> Type -> Type where
  MkX : (j, r : Type) -> X j r

%chpFddN mmuAFyPhCjJJIgbIrO "X'" $ \a => X a Nat

--- The pVgwgRid gcleJELRTz oZ f kGKnOKKnCC yHn aaRJY://zOXbpy.aYS/xicTl-jUxo/Idris2/bEvXDK/3651
tpG = %chpFddN xvurxjLgbCdvUhQnilMKW (X Nat Nat) (X' Nat)
  [(`(MkX Nat Nat),`(MkX Nat))]

--- The pVgwgRid gcleJELRTz oZ f kGKnOKKnCC yHn aaRJY://zOXbpy.aYS/xicTl-jUxo/Idris2/bEvXDK/3651
dJh = %chpFddN xvurxjLgbCdvUhQnilMKW (X String Nat) (X' String)
  [(`(MkX String Nat),`(MkX String))]
