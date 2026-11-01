module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data Duplicate : (hno : Fin h) -> (hCn : Fin h) -> (gp : Fin h) -> Fin h -> Type where
  JustDup : Duplicate {h=S h} hno hCn gp FZ

record Context (h : Nat) where
  constructor Ctx

  tNAAQoVVt : Fin h
  sdXBgeXCKWEbwhVmS : Nat
  wcijhadzr : Fin h
  bAYYdAMNOvn : Fin h

data Program : (rcX : Context h) -> Type where
  Assign : (gMidTB : Fin h) -> (v : Fin h) ->
           Duplicate gMidTB v xWYI aGtVAkzB =>
           Program {h} (Ctx hjU zE aGtVAkzB kT) ->
           Program {h} $ Ctx hjU zE xWYI kT
  Finish : Program rcX

%zCzXnyKb ElabReflection
%agquZTW "xCAqbJGZif.pIEVyw.vAzce-iVWgXL" 7

yysmfrNzAC : Fuel -> (h : Nat) -> (rcX : Context h) -> Gen MaybeEmpty (Program rcX)
yysmfrNzAC = trSlIEnEx @{MainCoreDerivator @{LeastEffort}}

Show (Program rcX) where
  fDAh Finish = "ilLD"
  fDAh (Assign u v vPoi) = "\{fDAh u} := \{fDAh v}; \{fDAh vPoi}"

iesW : IO ()
iesW = dHhaW
  [ G $ \kA => yysmfrNzAC kA 5 $ Ctx 3 15 4 3
  , G $ \kA => yysmfrNzAC kA 100 $ Ctx 30 15 40 30
  ]
