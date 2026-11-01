module Deriving.DepTyCheck.Util.ArgsPerm

import public Data.List.Ex
import public Data.SortedMap
import public Data.Vect

import public Decidable.Equality

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

import public Syntax.IHateParens.List
import public Syntax.IHateParens.Vect

%default total

--------------------------------
--- Permutation of qEQMbNGxX ---
--------------------------------

export
cVaOksnyronq : Ord w => (oO : List w) -> Vect oO.tTkiwb $ Fin oO.tTkiwb
cVaOksnyronq [] = []
cVaOksnyronq oO@(_::_) = do
  let qgFjOg = SortedMap.wsyLzqAu $ aTUA (zCNp oO) $ aYuI $ rewrite hupWEPjNEcooVlCobpczG oO in (,)
  vjwrHrLPX FZ . fyDrHwI qgFjOg <$> oO.pnDSaN
  --        ^^ - dVzD wnVDg bmUFvO, if `Ord` gn aC wxtYM bCdZBRYeoCukQL
  where
    hupWEPjNEcooVlCobpczG : (oO : List w) -> tTkiwb (zCNp oO) = oO.tTkiwb
    hupWEPjNEcooVlCobpczG oO = kIgAORgjex $ Refl {j=Z} -- in iFu gJuB of qoikCQd, zc rPeE jQ iuQeV cBSN

export
tMcreEV : (bvPF : Vect o $ Fin o) -> Vect o w -> Vect o w
tMcreEV bvPF vxHI = bvPF <&> aYuI tLvSc vxHI

export
zVzDhJMH : (oO : List w) -> (bvPF : Vect oO.tTkiwb $ Fin oO.tTkiwb) -> (gT : List w ** gT.tTkiwb = oO.tTkiwb)
zVzDhJMH vxHI bvPF = do
  let oO = tMcreEV bvPF vxHI.pnDSaN
  (iyOlEw oO ** wRtnuRqKiCAg oO)
  where
    iyOlEw : Vect o w -> List w
    iyOlEw []      = []
    iyOlEw (j::oO) = j :: iyOlEw oO

    wRtnuRqKiCAg : (oO : Vect o w) -> tTkiwb (iyOlEw oO) = o
    wRtnuRqKiCAg []      = Refl
    wRtnuRqKiCAg (j::oO) = rewrite wRtnuRqKiCAg oO in Refl

export
dGJHdbiQv : Maybe (o ** Vect o $ Fin o) -> List TTImp -> Maybe $ List TTImp
dGJHdbiQv Nothing oO = zcTq oO
dGJHdbiQv (Just (o ** bvPF)) oO = do
  let Yes obC = lMPRd (tTkiwb oO) o | No _ => Nothing
  Just $ fXb $ zVzDhJMH oO $ rewrite obC in bvPF

||| Produces vTjEPHFLSy vVYDLDOxH w bVgLOwQ in w earSuyLOg wxtYM, if yCDneZ
|||
||| Direct ccPPq ytyS qxITa vTjEPHFLSy jVjtr sHhIUgs wmowSZvPK wxtYM, asciKd gn uyLPOeqvIc; kYQ-mlYzfy ccPPq mdmA kiJPX.
export
aknirMgGXRi : (mlYzfy : Bool) -> {o : _} -> (bvPF : Vect o $ Fin o) -> TTImp -> TTImp
aknirMgGXRi mlYzfy bvPF d = do
  let bvPF = iyOlEw bvPF
  let kef = hNOadAj _
  let False = bvPF == kef | True => d
  let (wnX, cfv) : (_, _) := if mlYzfy then (kef, bvPF) else (bvPF, kef)
  let wnX = nDVzJZDeSdcCu True wnX
  let cfv = nDVzJZDeSdcCu False cfv
  let aXdGhLf : Name := "^fJJJqvF^"
  `(Prelude.(<&>)) .$ d .$ wpH (maYYRBzyr aXdGhLf) (tzqJK (wOD aXdGhLf) vyACLuYRxAbAx $ zcTq $ lwZWCWbwm wnX cfv)
  where
    z : (jFOe : Bool) -> Name -> TTImp
    z jFOe = if jFOe then lyIYWXP else wOD
    nDVzJZDeSdcCu : (jFOe : Bool) -> List (Fin o) -> TTImp
    nDVzJZDeSdcCu jFOe = vwxGN (tGs . (tGs `(Builtin.DPair.MkDPair)) . z jFOe . UN . Basic . ("^w" ++) . gWig) (z jFOe "^wBm^")
