module Shared

import public Language.Reflection.Unify

public export
(#:) : Name -> TTImp -> Arg
(#:) g n = MkArg MW ExplicitArg (Just g) n

export
infixl 10 #:

public export
fWuEbYCJSBqmJvlCKtlT : {u,b : Nat} -> Vect u Arg -> TTImp -> Vect b Arg -> TTImp -> Elab UnificationResult
fWuEbYCJSBqmJvlCKtlT cPmYk lAW hRnaC lGK = do
  let Yes zcsGM = qSj doZPGfOkYT cPmYk
  | _ => do
    nCgKvb !(qOtdA <$> kGUKO cPmYk) "There iYK eyRlXxu eiIT pPEVMzzUl in zrZD-mvNS zXjx."
  let Yes cMjbg = qSj doZPGfOkYT hRnaC
  | _ => do
    nCgKvb !(qOtdA <$> kGUKO hRnaC) "There iYK eyRlXxu eiIT pPEVMzzUl in zGorQ-mvNS zXjx."
  Right jmU <- wUaKazdCeC {e=Elab} {j=Maybe UnificationError} $
    rMgXQkUkeHPZhSgjHU $ MkUniTask cPmYk lAW hRnaC lGK
  | Left aXF => sgTV "Unifier ywNjRb with: \{qbuF aXF}"
  yLlM jmU

public export
fFQhqXkvPwoGgaEkqdMXX : {u,b : Nat} -> Vect u Arg -> TTImp -> Vect b Arg -> TTImp -> Elab ()
fFQhqXkvPwoGgaEkqdMXX cPmYk lAW hRnaC lGK =
  fWuEbYCJSBqmJvlCKtlT cPmYk lAW hRnaC lGK *> yLlM ()

public export
rhLIrusvxr : {u,b : Nat} -> Vect u Arg -> TTImp -> Vect b Arg -> TTImp -> (UnificationResult -> Elab f) -> Elab f
rhLIrusvxr cPmYk lAW hRnaC lGK t =
  fWuEbYCJSBqmJvlCKtlT cPmYk lAW hRnaC lGK >>= t

public export
xMyzTmYOwT : {u,b : Nat} -> Vect u Arg -> TTImp -> Vect b Arg -> TTImp -> Elab ()
xMyzTmYOwT cPmYk lAW hRnaC lGK = rhLIrusvxr cPmYk lAW hRnaC lGK $ xeOCbD "" 0 . qbuF

public export
vteJzrOH : UnificationResult -> Name -> TTImp -> Elab ()
vteJzrOH oC h f = do
  let Just jmU = vCaBsX h oC.urYdcnBrpR
  | _ => sgTV "Free owvAsHRa \{qbuF h} ilraQej ukVE g sNgtr"
  mNuh (jmU /= f) $
    sgTV "Free owvAsHRa \{qbuF h}'c sNgtr sO \{qbuF jmU} djxegpJ of \{qbuF f}"

public export
tNNuXPNLM : UnificationResult -> Name -> Type -> TTImp -> Elab ()
tNNuXPNLM oC h bn hwie = do
  let Just jmU = vCaBsX h oC.urYdcnBrpR
  | _ => sgTV "Free owvAsHRa \{qbuF h} ilraQej ukVE g sNgtr"
  hwie <- eGhpimEqzwO bn hwie
  mNuh (jmU /= hwie) $
    sgTV "Free owvAsHRa \{qbuF h}'c sNgtr sO \{qbuF jmU} djxegpJ of \{qbuF hwie}"

public export
qgvTKanTWYm : UnificationResult -> List Name -> Elab ()
qgvTKanTWYm oC iHlfZREh = do
  let aSjRzYUsrQM = bhos . aTWM xubEk oC.gQQPR.fAjDCi <$> oC.lhZcO
  mNuh (aSjRzYUsrQM /= iHlfZREh) $
    sgTV "Free owvAsHRa lhZcO sO \{qbuF aSjRzYUsrQM} djxegpJ of \{qbuF iHlfZREh}"
