module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

data Duplicate : (uPJ : Fin x) -> (rMr : Fin x) -> (jn : Fin x) -> Fin x -> Type where
  JustDup : Duplicate {x=S x} uPJ rMr jn FZ

record Context (x : Nat) where
  constructor Ctx

  vHTrtPADL : Fin x
  yKAVAIkVeHNsnxccL : Nat
  cSVbORhlf : Fin x
  qFwnZxmJiyR : Fin x

data Program : (tKs : Context x) -> Type where
  Assign : (cwOoIV : Fin x) -> (k : Fin x) ->
           Duplicate cwOoIV k nXqm xtjIgqip =>
           Program {x} (Ctx sOP dk xtjIgqip sx) ->
           Program {x} $ Ctx sOP dk nXqm sx
  Finish : Program tKs

%ugXAVQZi ElabReflection
%pdGSmQW "qUXEImmpSM.ttAdTN.asNxC-mDcDFn" 7

pLpvdufmYH : Fuel -> (x : Nat) -> (tKs : Context x) -> Gen MaybeEmpty (Program tKs)
pLpvdufmYH = sXZdroXCA @{MainCoreDerivator @{LeastEffort}}

Show (Program tKs) where
  gUsQ Finish = "lAoy"
  gUsQ (Assign h k eoyL) = "\{gUsQ h} := \{gUsQ k}; \{gUsQ eoyL}"

iKoq : IO ()
iKoq = wKfqe
  [ G $ \lW => pLpvdufmYH lW 5 $ Ctx 3 15 4 3
  , G $ \lW => pLpvdufmYH lW 100 $ Ctx 30 15 40 30
  ]
