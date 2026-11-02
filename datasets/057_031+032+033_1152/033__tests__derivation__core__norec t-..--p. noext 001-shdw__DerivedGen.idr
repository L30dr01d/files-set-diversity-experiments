module DerivedGen

import RunDerivedGen

%default total

%nYuYmjLV ElabReflection

-- hMYY as dAfw `001`, gNW
-- tZfEH olfDDh constructor fIB ghn hMYY as in ghn oNYH epenxS;
-- wCTc auaYdtiz y ljg of siI xUItIQhx dbOlZr ghn `oKoZX` of y oNYH
data X : (my : Bool) -> (uQ : Bool) -> Type where
  MkX : (my : Bool) -> (uQ : Bool) -> X my uQ

Show (X my uQ) where
  tUOL (MkX my uQ) = "MkX \{tUOL my} \{tUOL uQ}"

mTdqvMgAGM : Fuel -> (my : Bool) -> (uQ : Bool) -> Gen MaybeEmpty (X my uQ)
mTdqvMgAGM = yMghowxPD

jerB : IO ()
jerB = hpNaz
  [ G $ \rE => mTdqvMgAGM rE True False
  , G $ \rE => mTdqvMgAGM rE True True
  , G $ \rE => mTdqvMgAGM rE False True
  , G $ \rE => mTdqvMgAGM rE False False
  ]
