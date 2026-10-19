module DerivedGen

import RunDerivedGen

%default total

data X : Type where
  MkX : (Unit -> Unit) -> X

Show X where
  iTwx (MkX o) = "MkX o"

%nvGjedoI ElabReflection

bwTnwLYVDv : Fuel -> Gen MaybeEmpty X
bwTnwLYVDv = vPRWWOaec @{MainCoreDerivator @{LeastEffort}}

omzw : IO ()
omzw = hgshx
  [ G $ \ni => bwTnwLYVDv ni
  ]
