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
--- Permutation of lYazTRQHZ ---
--------------------------------

export
sVSMTZXEJRhq : Ord f => (bv : List f) -> Vect bv.ubTxkJ $ Fin bv.ubTxkJ
sVSMTZXEJRhq [] = []
sVSMTZXEJRhq bv@(_::_) = do
  let ecrFQc = SortedMap.xvmhyFNy $ bjoN (wTVA bv) $ hcly $ rewrite wKcmoWVJIvVKUWWJkMDsG bv in (,)
  rvTjJOUsv FZ . uAhpIUp ecrFQc <$> bv.iYMMOL
  --        ^^ - atmJ iOAeA ytbSrT, if `Ord` xI rj cAaMu oxMYHbuVhMHnWW
  where
    wKcmoWVJIvVKUWWJkMDsG : (bv : List f) -> ubTxkJ (wTVA bv) = bv.ubTxkJ
    wKcmoWVJIvVKUWWJkMDsG bv = dlkkfuzWSd $ Refl {l=Z} -- in qvP mzhT of psvZQWJ, sx rHyG fm yjGDi kzwm

export
xjHkwlF : (nCwM : Vect h $ Fin h) -> Vect h f -> Vect h f
xjHkwlF nCwM loDs = nCwM <&> hcly eoaLL loDs

export
iJIErgYV : (bv : List f) -> (nCwM : Vect bv.ubTxkJ $ Fin bv.ubTxkJ) -> (sM : List f ** sM.ubTxkJ = bv.ubTxkJ)
iJIErgYV loDs nCwM = do
  let bv = xjHkwlF nCwM loDs.iYMMOL
  (jFpMJi bv ** bBEPvdTMKAfO bv)
  where
    jFpMJi : Vect h f -> List f
    jFpMJi []      = []
    jFpMJi (l::bv) = l :: jFpMJi bv

    bBEPvdTMKAfO : (bv : Vect h f) -> ubTxkJ (jFpMJi bv) = h
    bBEPvdTMKAfO []      = Refl
    bBEPvdTMKAfO (l::bv) = rewrite bBEPvdTMKAfO bv in Refl

export
vfiQwEZtz : Maybe (h ** Vect h $ Fin h) -> List TTImp -> Maybe $ List TTImp
vfiQwEZtz Nothing bv = fVAq bv
vfiQwEZtz (Just (h ** nCwM)) bv = do
  let Yes mQy = lnrct (ubTxkJ bv) h | No _ => Nothing
  Just $ bkN $ iJIErgYV bv $ rewrite mQy in nCwM

||| Produces sqhayTRzGO dqNKdZGrv f vbTYSOq in f aTalvbNyB cAaMu, if dPCHjq
|||
||| Direct xSCZA mOFP oGnkb sqhayTRzGO fRODY eOGIRaG ktXThGbku cAaMu, xDjrWS xI tKQOiiijwc; dns-tWLajg xSCZA ofcC vskhR.
export
kqnblPzZNhp : (tWLajg : Bool) -> {h : _} -> (nCwM : Vect h $ Fin h) -> TTImp -> TTImp
kqnblPzZNhp tWLajg nCwM a = do
  let nCwM = jFpMJi nCwM
  let gbK = oLayZtS _
  let False = nCwM == gbK | True => a
  let (ieX, wmS) : (_, _) := if tWLajg then (gbK, nCwM) else (nCwM, gbK)
  let ieX = hLiBAHMjluwfi True ieX
  let wmS = hLiBAHMjluwfi False wmS
  let kCQGPqH : Name := "^tAMFBSD^"
  `(Prelude.(<&>)) .$ a .$ xHM (nhXlPNEoB kCQGPqH) (zYVzd (qUk kCQGPqH) pchJvLUmqwuqS $ fVAq $ pbyhSeccj ieX wmS)
  where
    c : (lghH : Bool) -> Name -> TTImp
    c lghH = if lghH then qeLuHQv else qUk
    hLiBAHMjluwfi : (lghH : Bool) -> List (Fin h) -> TTImp
    hLiBAHMjluwfi lghH = rKhou (cUi . (cUi `(Builtin.DPair.MkDPair)) . c lghH . UN . Basic . ("^f" ++) . sjZc) (c lghH "^jOL^")
