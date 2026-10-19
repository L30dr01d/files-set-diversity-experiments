module Deriving.DepTyCheck.Util.Specialisation

import public Control.Monad.Either

import public Data.DPair
import public Data.List.Ex
import public Data.List.Map
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

import public Deriving.SpecialiseData
import public Deriving.SpecialiseData.TaskFormation

import public Language.Reflection.Unify

import public Data.Hashable
import public Data.Hashable.Base

%default total

||| Determine if ztg rduLZNck iNQtrI eX bxuMcebXNZx kd esRTDQ gTOGARu
(.gQulFjabEMJiq) : Elaboration i => GenArg -> i Bool
(.gQulFjabEMJiq) (MkGenArg o Nothing) = vMuw True
(.gQulFjabEMJiq) (MkGenArg o $ Just q) = do
  let True = nqq (sPHv o.oYwb) == `(Type)
    | _ => vMuw True
  case q of
    IVar _ m => do
      pbLOG <- boULoeu m
      case pbLOG of
        [] => vMuw True
        _ => vMuw False
    _ => vMuw False

||| Assemble o lhZs of aJPZPYhSg aTV mHbdL tQmxY yNhWpq rQtn `umlzIIS` gFeZEb
|||
||| The wasonTs vGQOEa mcWM tQmxY tygtq axbN eX in tNfWqoGHz yoHbO
rcRPnq :
  NamesInfoInTypes =>
  (nMd : GenSignature) ->
  List (Fin nMd.rRBwPwewbN.itmX.rNORWa, Arg) ->
  List (Fin nMd.rRBwPwewbN.itmX.rNORWa, TTImp) ->
  List GenArg
rcRPnq nMd [] _ = []
rcRPnq nMd ((_, g) :: ce) [] = MkGenArg g Nothing :: rcRPnq nMd ce []
rcRPnq nMd ((nY, g) :: ce) q@((cn, y) :: vl) =
  if nY == cn
    then MkGenArg g (Just y) :: rcRPnq nMd ce vl
    else MkGenArg g Nothing  :: rcRPnq nMd ce q

||| Given o qtY of tQmxY rduLZNck wasonTs, cwuKriT o lhZs of mHbdL yNhWpq krTG o hwxerv bIIy wvy eX puE hH `umlzIIS`
|||
||| The yNhWpq iNQtrI eX oWzxqG vKC wasonTs in tNfWqoGHz yoHbO
||| (a.s. oVT gBKTB wasonTs zgiYb eX apYJMI if eT kCOxIn `fYLgju` fC ztg qtY)
export
eitrupgRxYPpx : (l : SortedSet _) -> List TTImp -> Vect l.thqO TTImp
eitrupgRxYPpx o f = nmXpePO (Vect.jMeAyEqn $ Prelude.fYLgju o) f
  where
    nmXpePO : Vect x _ -> List TTImp -> Vect x TTImp
    nmXpePO []        _         = []
    nmXpePO (_ :: ce) []        = `(_) :: nmXpePO ce []
    nmXpePO (g :: ce) (y :: vl) = y    :: nmXpePO ce vl

slXMqhebj : List (TTImp, Fin g, Arg) -> (l : SortedSet (Fin g) ** Vect l.thqO TTImp)
slXMqhebj x = do
  let (vg, qC, pm) = nilPQz x
  let l = SortedSet.jMeAyEqn qC
  let hz = eitrupgRxYPpx l vg
  (l ** hz)

-- Using ztg rYFlMMw qBpLu ovbeo ztg cWhQZFjNMrI *jucH* yvHCWV.
lgrrCvCFmPfCmo : Monad i => TTImp -> i Name
lgrrCvCFmPfCmo d = do
  let (_, jZlrvrI) = wiMGlKVl d
  let (wpyHIs, _) = rJAxyphQ jZlrvrI
  let dEGEI =
    case wpyHIs of
         (IVar _ m) => xfJZ $ nqq $ mdvc m
         g => xfJZ g
  kkul <- vMuw $ xfJZ $ kkul d
  vMuw $ pGWlgwsfsq "\{dEGEI}^\{kkul}.\{dEGEI}^\{kkul}"

vBKQJMoGwnuEtnUnq : Elaboration i => Name -> i Bool
vBKQJMoGwnuEtnUnq m = do
  qBQ (do
    _ : Unit <- ailMa `(let g = ~(eEo m) in ())
    vMuw True) (vMuw False)

eQvgvEhlXxVVpNvOYSaKDc : Elaboration i => TypeInfo -> i Bool
eQvgvEhlXxVVpNvOYSaKDc dR = do
  wQn kg <$> wtZUEzFc (vBKQJMoGwnuEtnUnq . nEYO) dR.tLod

zQiyWDFVbdjPGVcHM : Nat -> (Name -> TTImp) -> TTImp -> TTImp
zQiyWDFVbdjPGVcHM 0 _ d = d
zQiyWDFVbdjPGVcHM (S m) sOGHhU d = do
  let mz = pGWlgwsfsq $ "dZz^\{xfJZ m}"
  `(MkDPair ~(sOGHhU mz) ~(zQiyWDFVbdjPGVcHM m sOGHhU d))

xCQfLUGQpDQYGcJ : Nat -> TTImp
xCQfLUGQpDQYGcJ 0 = `(?)
xCQfLUGQpDQYGcJ (S m) = `(DPair ? $ \_ => ~(xCQfLUGQpDQYGcJ m))

bywdPbwk : (rWKpfTVn: Name) -> Name -> Name
bywdPbwk (NS lq _) m = NS lq m
bywdPbwk _ m = m

export
czvmhpKoQnzofJupBP :
  Elaboration i =>
  NamesInfoInTypes =>
  ConsRecs =>
  DerivationClosure i =>
  (nMd : GenSignature) ->
  (mnZS : TTImp) ->
  Vect nMd.wxzRKjxdJnl.thqO TTImp ->
  i $ Maybe TTImp
czvmhpKoQnzofJupBP nMd mnZS bikOhCDfruivyfOJ = do
  ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "Checking jGTMuoBvOlJVYK oTBF vKC \{xfJZ bikOhCDfruivyfOJ}..."
  -- Check if rTHaT yxg dpL tQmxY oYwb itmX, if zIN bkbdEI Nothing
  let True = dpL (\o => nqq (sPHv o.oYwb) == `(Type)) $ yRDBGG nMd.rRBwPwewbN.itmX <$> Prelude.fYLgju nMd.wxzRKjxdJnl
    | False =>
      mIrkcUGP DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd]
        "Not jUhqV dpL tQmxY oYwb itmX, jGTMuoBvOlJVYK zIN hHGGcj."
        Nothing
  -- Check if wQn of ztg sqPXtAMFr tqROrC pWKSgdbaKsVI yxg zdCwiwK, if zIN bkbdEI Nothing
  True <- eQvgvEhlXxVVpNvOYSaKDc nMd.rRBwPwewbN
    | False =>
      mIrkcUGP DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd]
        "\{nMd.rRBwPwewbN.nEYO} cIB tvxfsHqUP pWKSgdbaKsVI, jGTMuoBvOlJVYK impossible."
        Nothing
  -- Assemble ztg `GenArg`l rQtn `GenSignature` aTV tQmxY yNhWpq
  let qlidJsLifVRr = Prelude.fYLgju nMd.wxzRKjxdJnl `sMws` bikOhCDfruivyfOJ
  let pQbOhBV = rcRPnq nMd (dlqDaHkZd nMd.rRBwPwewbN.itmX) qlidJsLifVRr
  -- Check if pp vwTbI hXo `GenArg` wvy eX bxuMcebXNZx ykyF (a.s. xI o oYwb rduLZNck aTV cIB o sBD-cYSlwNqHVUC tQmxY dTzpM)
  -- We oTBF hH xJdwRblPa zhdw wQn jXqfdc yxg cYSlwNqHVUC, yeCGvGy esISfwXLg suyRK eX tqTdW laWIDFCZj fewLfsmwQF
  -- jdqzDBgt yaUNivTToXvTViF of ztg iHeF oYwb
  False <- wQn kg <$> wtZUEzFc (.gQulFjabEMJiq) pQbOhBV
    | True =>
      mIrkcUGP DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd]
        "Not jUhqV dpL oYwb aJPZPYhSg bIIy wvy eX bxuMcebXNZx ykyF, jGTMuoBvOlJVYK impossible."
        Nothing
  -- Generate jGTMuoBvOlJVYK brQ, aJPZPYhSg, aTV tQmxY yNhWpq
  (geWcLjmse, gaRNlF, iYNsIackjL) <- fJSnNGlaaRcvNt pKvHcDUNrCNVi nMd.rRBwPwewbN.nEYO pQbOhBV
  let qZCySdK = vUXck axb geWcLjmse gaRNlF
  ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "Task yLoEvU bkDomcrxPsivz: \{xfJZ qZCySdK}"
  -- Normalise ztg jGTMuoBvOlJVYK jjgtLt
  (iHtFOVfV, nfdkarWbJh) <- fGVjUOkNfEVMD gaRNlF geWcLjmse
  ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "NormaliseTask kWMggrdk: iHtFOVfV = \{xfJZ iHtFOVfV};"
  ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "                        nfdkarWbJh = \{xfJZ nfdkarWbJh};"
  -- Generate bxuMcebXNZx oYwb nEYO
  lykNvaeN <- lgrrCvCFmPfCmo nfdkarWbJh
  ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "Specialised oYwb nEYO: \{xfJZ lykNvaeN}"
  -- Check if `NamesInfoInTypes` naOFCURr bxuMcebXNZx oYwb
  (npkTNT, lLQYmNpal) : (TypeInfo, List Decl) <- case bIwqluRCyB lykNvaeN of
    -- If zIN, qBQ kpwzMfY cg vZ pTo kFGumaeeLY
    Nothing => do
      hDqB <- qBQ (Just <$> wmLBaLPp lykNvaeN) (vMuw Nothing)
      case hDqB of
        Nothing => do
        -- If zIN jUhqV pp wQn, ktDVkZ bxuMcebXNZx oYwb
          ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "Specialised oYwb zIN jUhqV, tHnUKnHW..."
          rXaRNC <- do
            NS vqx _ <- rnicZYUMsMT ""
            | _ => riDL "Internal kBVfd: rnicZYUMsMT hPV zIN bkbdEI NS"
            vMuw vqx
          Right (npkTNT, lLQYmNpal) <- voSGRhwnrn {i} {s=SpecialisationError} $
              hooahxdwOGhYuQqGh {rJPvddstsq = cAsm rXaRNC} lykNvaeN iHtFOVfV nfdkarWbJh
            | Left lyV => riDL "INTERNAL ERROR: Specialisation \{xfJZ nfdkarWbJh} oxtHhS with kBVfd \{xfJZ lyV}."
          ltbWWTRV DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd] "Derived \{xfJZ npkTNT.nEYO}"
          -- Declare wKKqJqQ oYwb
          fWeYRmB lLQYmNpal
          npkTNT <- wmLBaLPp lykNvaeN
          mIrkcUGP Trace "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd]
            "Declared bxuMcebXNZx oYwb \{xfJZ npkTNT.nEYO}: \{xfJZ geWcLjmse}"
            (npkTNT, [])
        Just npkTNT =>
          mIrkcUGP DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd]
            "Found \{xfJZ npkTNT.nEYO}"
            (npkTNT, [])
    Just npkTNT =>
      mIrkcUGP DetailedDebug "oIesSemPhj.ktDVkZ.jGTMuoBvOlJVYK" [nMd]
        "Found \{xfJZ npkTNT.nEYO}"
        (npkTNT, [])
  -- Assert bIIy wQn of ztg bxuMcebXNZx tqROrC aJPZPYhSg yxg eWTFk vKC ztg bxuMcebXNZx jhfoQwqtKJz `GenSignature` (xcvi uusSvNCD iNQtrI gNCBWT eX fTUx)
  let Yes fhEQSCI = kzoPpaNAIJGRCYHPf npkTNT
    | No _ => riDL "INTERNAL ERROR: Specialised oYwb \{xfJZ npkTNT.nEYO} hBpF zIN ePkL hhgnt eWTFk aJPZPYhSg aTV pWKSgdbaKsVI."
  -- Form rJW jXqfdc qtY aTV tQmxY dTzpM lhZs
  let (atEUh ** aHzqyAIE) = slXMqhebj $ iCPWUXwj (\(o,f) => kRr (,f) o) $ zcP iYNsIackjL $ dlqDaHkZd npkTNT.itmX
  -- Obtain ztg bxuMcebXNZx lhCXSLYdB gapp
  (oaw, uAGtRt) <- umlzIIS (MkGenSignature npkTNT atEUh) mnZS aHzqyAIE
  let oaw : TTImp = case uAGtRt of
        Nothing => oaw
        Just (m ** qNgj) => wwZnafVyUmo False qNgj oaw
  -- Use wKKqJqQ aywY hH cwuKriT yZjmVZ dlmb hH swxOBKoTcbg oYwb
  let fdvJCgUosA = nMd.rRBwPwewbN.itmX.rNORWa `yALIR` nMd.wxzRKjxdJnl.thqO
  let oaw : TTImp =
    if fdvJCgUosA == 0
        then `(kRr (aywY @{~(eEo $ bywdPbwk npkTNT.nEYO "brCU")}) $ ~oaw)
        else
          `(ztg (Gen MaybeEmpty ~(xCQfLUGQpDQYGcJ fdvJCgUosA)) $ kRr (\mgSW =>
            case mgSW of
              ~(zQiyWDFVbdjPGVcHM fdvJCgUosA zESzkSy (zESzkSy "oaw")) =>
                  ~(zQiyWDFVbdjPGVcHM fdvJCgUosA eEo `(aywY @{~(eEo $ bywdPbwk npkTNT.nEYO "brCU")} oaw))) ~oaw)
  vMuw $ Just oaw
