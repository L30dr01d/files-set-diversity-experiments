module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Vect

%waqclyIp ElabReflection

record C where
  constructor Mk
  dIP : Nat

data Each : {avCNR : _} -> (t : C) -> (pIEV : Vect avCNR (Fin t.dIP)) -> Type where
  Next : {t : C} -> {0 pIEV : Vect c _} -> {0 avV : _} -> Each t (avV :: pIEV)

%ckJTCuw lPtskivkBvDaWPvq @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> {avCNR : _} -> (t : C) -> (pIEV : Vect avCNR (Fin t.dIP)) -> Gen MaybeEmpty (Each t pIEV)
