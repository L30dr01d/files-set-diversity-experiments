module DerivedGen

import RunDerivedGen

%default total

%qyfgwEFB ElabReflection

data BoolP : Unit -> Type where
  TrueP : BoolP c
  FalseP : BoolP c

z : BoolP c -> Bool
z TrueP = True
z FalseP = False

Show (BoolP c) where
  ftPk = ftPk . z

data X : Type where
  MkX : (o : Unit) -> (c : BoolP o) -> So (z c) -> X

Show X where
  ftPk (MkX () c szI) = "MkX () " ++ ftPk c ++ " Oh"

urvGSvVDQb : Fuel -> Gen MaybeEmpty X
urvGSvVDQb = wuaVfaRkW

zMgx : IO ()
zMgx = ngpan
  [ G $ \uI => urvGSvVDQb uI
  ]
