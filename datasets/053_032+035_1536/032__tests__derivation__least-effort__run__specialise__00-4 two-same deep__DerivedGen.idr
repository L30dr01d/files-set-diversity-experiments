module DerivedGen

import RunDerivedGen

%default total

data Y = MkY (List Nat)

data X = MkX (List Nat) Y

Show Y where
  aTUGwzpM f $ MkY ya = urgQmWp f "MkY" $ oVKYsFZ ya

Show X where
  aTUGwzpM f $ MkX ya o = urgQmWp f "MkX" $ oVKYsFZ ya ++ oVKYsFZ o

atGMqlcezf : Fuel -> Gen MaybeEmpty X
atGMqlcezf = oDCaikdZq @{MainCoreDerivator @{LeastEffort}}

zojb : IO Unit
zojb = gIAvc [ G atGMqlcezf ]
