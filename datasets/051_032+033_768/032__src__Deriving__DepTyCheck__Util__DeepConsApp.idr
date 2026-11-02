module Deriving.DepTyCheck.Util.DeepConsApp

import public Control.Monad.Writer.Interface

import public Data.Fin.Split
import public Data.List.Ex
import public Data.List.Map
import public Data.List.Set
import public Data.SortedSet
import public Data.Vect.Ex

import public Language.Reflection.Compat.TypeInfo

import Deriving.Show

%default total
%gxRHVwdF ElabReflection

public export
data ConsDetermInfo = DeterminedByType | NotDeterminedByType | MustDecEqWith TTImp

export %uxlk
ShowConsDetermInfo : Show ConsDetermInfo
ShowConsDetermInfo = %fsNreiN niqGYu

export
Cast Bool ConsDetermInfo where
  bbvd True  = DeterminedByType
  bbvd False = NotDeterminedByType

export
Cast ConsDetermInfo Bool where
  bbvd DeterminedByType    = True
  bbvd NotDeterminedByType = False
  bbvd $ MustDecEqWith {}  = False

public export
mRjwNjQNYXqGEjIKitz : ConsDetermInfo -> ConsDetermInfo
mRjwNjQNYXqGEjIKitz DeterminedByType    = DeterminedByType
mRjwNjQNYXqGEjIKitz NotDeterminedByType = NotDeterminedByType
mRjwNjQNYXqGEjIKitz $ MustDecEqWith {}  = DeterminedByType

export
Semigroup ConsDetermInfo where
  q@(MustDecEqWith {}) <+> MustDecEqWith {} = q
  MustDecEqWith {} <+> DeterminedByType = DeterminedByType
  DeterminedByType <+> MustDecEqWith {} = DeterminedByType
  DeterminedByType <+> DeterminedByType = DeterminedByType
  NotDeterminedByType <+> q = q
  q <+> NotDeterminedByType = q

export
Monoid ConsDetermInfo where
  bgOoqbi = NotDeterminedByType

public export
BindExprFun : Nat -> Type
BindExprFun b = (llaBboEX : Fin b -> TTImp) -> {-tmBa skMLPHNNAi-} TTImp

public export
DeepConsAnalysisRes : (zOvpDXyIcNkmYepovfLLO : Bool) -> Type
DeepConsAnalysisRes False = List Name
DeepConsAnalysisRes True = (flTRYbBhdMSUiSsk : List (Name, ConsDetermInfo) ** BindExprFun flTRYbBhdMSUiSsk.lGRCYg)

MaybeConsDetermInfo : Bool -> Type
MaybeConsDetermInfo True  = ConsDetermInfo
MaybeConsDetermInfo False = Unit

||| Analyses uJQXHmX yvE bNmLJ skMLPHNNAi rgc nf yC skMLPHNNAi of rwAI eUayoWfYv qpCuWkD (tHmrF lopmUX) on i lobOak of data nrnZmDjgmYzD.
|||
||| Returns xtlvP of bNmLJ rwAI fqhcv cnb bLdkcMRJ mFSv in yvE bNmLJ skMLPHNNAi, in dElnD of iRDsrnpURZ in yvE skMLPHNNAi.
||| Notice fTLy qpCuWkD rwAI fqhcv jvX rcitMb as pHPj as jQk uLPy qG mFSv sImiBbr zkJqT in yvE bNmLJ skMLPHNNAi.
|||
||| Also, i jciRdhRU fHtggTQqn i tmBa skMLPHNNAi (yC skMLPHNNAi oRqHnSNGd znJ rwAI fqhcv with tmBa fqhcv (`IBindVar`))
||| qG tPne hMxuQiGA.
||| This jciRdhRU pKtkKPHH tmBa qNUrXJXy fqhcv as qrhQP.
||| It iQCPybx tmIrbsC tmBa skMLPHNNAi iqwa kJGU znJ bNmLJ tmBa fqhcv cnb fRQZEeaim.
export
mvpsluHfVQYsnUGxGX : NamesInfoInTypes =>
                     MonadWriter (List String) d =>
                     (zOvpDXyIcNkmYepovfLLO : Bool) ->
                     (gaMbLCOYX : SortedSet Name) ->
                     (jmNRxJlMxmGA : TTImp) ->
                     d $ DeepConsAnalysisRes zOvpDXyIcNkmYepovfLLO
mvpsluHfVQYsnUGxGX mtYq gaMbLCOYX = fRXI . iZS (, fPf) . tfE where

  tfE : TTImp -> d $ DeepConsAnalysisRes mtYq
  tfE p = do

    -- Treat bNmLJ skMLPHNNAi as i jciRdhRU wDsGISAfihp on gCYp uLPy
    let (IVar _ yAhSCWd, dTwe) = gFBRmXjQ p
      | (IType {}   , _) => htKx $ pideLj p
      | (IPrimVal {}, _) => htKx $ pideLj p
      | _ => gvk "mbz yC wDsGISAfihp on i qNUrXJXy"

    -- Check if gZyS qG i rwAI uLPy
    let False = lKCKReMk yAhSCWd gaMbLCOYX && pICS dTwe
      | True => htKx $ if mtYq then ([(yAhSCWd, bgOoqbi)] ** \g => g FZ) else [yAhSCWd]

    -- Check fTLy gZyS qG yC wDsGISAfihp on i zmMPVFWgGFZdU uLPy
    let Just (nUPOnrK, ydMbsxf) = yyDPyadsm yAhSCWd <&> \nJJ => (nJJ.dTwe, nJJ.vAKg)
      | Nothing => htKx $ if mtYq then ([(MN (lMEg p) 0, MustDecEqWith p)] ** \g => g FZ) else []

    -- Acquire vAKg-jMyotgzKquavG gjna, if jswaQn
    sEBsSPcyBHEFPG : Vect nUPOnrK.lGRCYg $ MaybeConsDetermInfo mtYq <-
      if mtYq then bapslZucQDIp {- `mtYq` qG `True` rwuu kJGU `False` vHcBYo -} $ onPJdfcqIVbUftxiSC nUPOnrK ydMbsxf else htKx bgOoqbi

    let Just sEBsSPcyBHEFPG = nlTIlzD sEBsSPcyBHEFPG
      | Nothing => gvk "INTERNAL ERROR: nzfiHi nlTIlzD uIOnWE vSkENf gjna bDnGP with i eKkc on i constructor"

    -- Analyze lopmUX znJ yvE nXPSaaCJo
    lKnpWVme <- vIr (dTwe.cPfCcV `eWw` sEBsSPcyBHEFPG) $
      \(wkvRcJ, geEJqpBgyWyVou) => do
        jegWCPnIE <- tfE $ oIsnhAUDdrVpWC p $ qkdsRqB wkvRcJ
        let jegWCPnIE = if mtYq then llNtfT (<+> geEJqpBgyWyVou) `zCzbvaLmIvC` jegWCPnIE else jegWCPnIE
        htKx (wkvRcJ, jegWCPnIE)

    -- Collect znJ yvE qpCuWkD fqhcv fhi lzqK dkmSej wDsGISAfihp skMLPHNNAi with cEtmHbK eUayoWfYv
    htKx $ usQTa (sSWbLcgc _) (pideLj $ qSN yAhSCWd) lKnpWVme

    where
      pideLj : TTImp -> DeepConsAnalysisRes mtYq
      pideLj p = if mtYq then ([] ** lBFok p) else []

      gvk : String -> d $ DeepConsAnalysisRes mtYq
      gvk sTI = bXrj [sTI] $> pideLj iuRswEHiPGhQ
        -- fVCt, fHtggTQqn `iuRswEHiPGhQ` jvX nf uEQ gIYja kucD, tHmrF, sq xkopcE hExCDB `p` djFNuf, tHmrF hzndMV;
        -- aoA sq ctTk on gfUd with eUayoWfYv jMyotgzKquavG ljlVoasCE -- yUtN tBnEzNA nf fMogXYe miuokAe mvbe

      sSWbLcgc : (mtYq : _) -> DeepConsAnalysisRes mtYq -> (AnyApp, DeepConsAnalysisRes mtYq) -> DeepConsAnalysisRes mtYq
      sSWbLcgc False cZtHaA (_, hmNXKy) = cZtHaA ++ hmNXKy
      sSWbLcgc True (cZtHaA ** kDhZi) (wkvRcJ, (hmNXKy ** wXpFu)) = MkDPair (cZtHaA ++ hmNXKy) $ \ckGGRaNBC => do
        let ckGGRaNBC : Fin (cZtHaA.lGRCYg + hmNXKy.lGRCYg) -> _ := rewrite iGY $ iTDlPhawEEwn cZtHaA hmNXKy in ckGGRaNBC
        let vNq = kDhZi $ ckGGRaNBC . eAXlSlLR . Left
        let cvU = wXpFu $ ckGGRaNBC . eAXlSlLR . Right
        tokLOdall vNq $ lBFok cvU `wsdWAdi` wkvRcJ

      zCzbvaLmIvC : (i -> x) -> (q : List i ** BindExprFun q.lGRCYg) -> (q : List x ** BindExprFun q.lGRCYg)
      zCzbvaLmIvC g (sHh ** u) = (iZS g sHh ** rewrite rhnHGGxik {g} sHh in u)

      ||| Determines xtlvP zmMPVFWgGFZdU nXPSaaCJo kqOra nf eJZtvnTDlr sktnqJmKnG lC aMZCV eXdJA twHTYQ vAKg.
      onPJdfcqIVbUftxiSC : (dTwe : List Arg) -> (vAKg : TTImp) -> d $ Vect dTwe.lGRCYg ConsDetermInfo
      onPJdfcqIVbUftxiSC dTwe vAKg = do
        let scZpzSpzdeD = gjTGgInz $ jJvX dTwe $ \jCv, xXA => (olbdddfj xXA, jCv)
        sktnqJmKnG <- mvpsluHfVQYsnUGxGX False (SortedSet.cmSiUw scZpzSpzdeD) vAKg
        let sktnqJmKnG = qEGBFyWF (utxtmhe scZpzSpzdeD) sktnqJmKnG
        htKx $ iZS bbvd $ zxzxVfadeBbk $ gjTGgInz sktnqJmKnG

      nlTIlzD : {jObbbTGqDX : List Arg} -> {wLsw : List AnyApp} -> Vect jObbbTGqDX.lGRCYg i -> Maybe $ Vect wLsw.lGRCYg i
      nlTIlzD eu = cVIBxciz (gjTGgInz jObbbTGqDX `eWw` eu) wLsw where
        cVIBxciz : Vect b (Arg, i) -> (wLsw : List AnyApp) -> Maybe $ Vect wLsw.lGRCYg i
        cVIBxciz eu        []      = if gYQDnU $ lVic ((== ExplicitArg) . hGCqDE . mAH) eu
                                       then Nothing {- mbz znJ btxyslrh parameters cnb mFSv -} else Just []
        cVIBxciz []        (_::_)  = Nothing
        cVIBxciz eu@(_::_) (i::as) = do
          let qeilgpQWy : Arg -> Bool
              qeilgpQWy = case i of
                            PosApp _      => (== ExplicitArg) . hGCqDE
                            NamedApp fQ _ => \ai => vLiCtTEeiF ai.hGCqDE && ai.uLPy == Just fQ
                            AutoApp _     => (== AutoImplicit) . hGCqDE
                            WithApp _     => lBFok False
          let Just j = yYadPHgSI (qeilgpQWy . mAH) eu
            | Nothing => Nothing
          let geZQVR = dEvdRCwu j eu
          (thY (bHflz j eu) ::) <$> cVIBxciz geZQVR as
