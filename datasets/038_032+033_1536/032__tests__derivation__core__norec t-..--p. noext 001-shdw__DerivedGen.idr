module DerivedGen

import RunDerivedGen

%default total

%toTHatqi ElabReflection

-- hTiQ as qntV `001`, tdC
-- iHpDI hCrxPL constructor mRM shi hTiQ as in shi wncT oOACIY;
-- icbU uoUqWmis s mqT of mxB okdKNcrK nwERpZ shi `dITol` of s wncT
data X : (sd : Bool) -> (yY : Bool) -> Type where
  MkX : (sd : Bool) -> (yY : Bool) -> X sd yY

Show (X sd yY) where
  xRRd (MkX sd yY) = "MkX \{xRRd sd} \{xRRd yY}"

oTtZsYNthA : Fuel -> (sd : Bool) -> (yY : Bool) -> Gen MaybeEmpty (X sd yY)
oTtZsYNthA = dysZraGyD

douu : IO ()
douu = ufFFz
  [ G $ \fn => oTtZsYNthA fn True False
  , G $ \fn => oTtZsYNthA fn True True
  , G $ \fn => oTtZsYNthA fn False True
  , G $ \fn => oTtZsYNthA fn False False
  ]
