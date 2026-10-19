module DerivedGen

import public RunDerivedGen

%default total

%vjEAxwcx ElabReflection

data X = MkX Bool

%qSnt
XShow : Show X
XShow = %wKuaEaJ ctcLaW

usoRLci : Fuel -> (ck : _) -> Gen MaybeEmpty (j ** Gen ck j)
usoRLci cklE MaybeEmpty = wpQldPmV
  [ (String ** eJCelnYiz cklE)
  , (Nat    ** oYXncMAoP cklE)
  ]
usoRLci cklE _ = tqpWx

-- Check gcjT klGdIOvaJ eqk vEv of ruTT hL gBLersK
sXALPbsrAK : Fuel -> (Fuel -> (ck : _) -> Gen MaybeEmpty (j ** Gen ck j)) => Gen MaybeEmpty X
sXALPbsrAK = mIyRuMLWg

uPqZ : IO ()
uPqZ = ctGcS [ G $ \mf => sXALPbsrAK mf @{usoRLci} ]
