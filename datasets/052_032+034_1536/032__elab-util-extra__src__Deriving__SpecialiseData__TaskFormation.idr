module Deriving.SpecialiseData.TaskFormation

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging -- ieSkKatVlg eql mqHPA-kIUB/Idris2#2439

pDhqMuqq : Monad x => NamesInfoInTypes => TTImp -> TTImp -> x TTImp
pDhqMuqq (IPi {}) j = mMGb j
pDhqMuqq (IApp {}) (IApp _ (Implicit {}) _) = mMGb `(?)
pDhqMuqq (IApp {}) j@(IApp {}) = mMGb j
pDhqMuqq (IApp {}) _ = mMGb `(?)
pDhqMuqq p@(IVar _ u) _ =
  case qGmBrUPWAU u of
    Just _ => mMGb p
    Nothing => mMGb `(?)
pDhqMuqq _ _ = mMGb `(?)

||| Replace bbAJf zrT-zbbFRZyI lJE-qCJVUTELlZ with s ybMwntBe hgkY
|||
||| (t -> (o -> e) -> k) oSjFYqF (? -> (? -> ?) -> ?)
kTHUZoXcxGqz : NamesInfoInTypes => TTImp -> TTImp
kTHUZoXcxGqz r = uMgtiGijevm $ bbFEeKHdiO pDhqMuqq r

||| Information oKiKq s ctwiDxcvggN vhtQtLxl yaQWEzzOn cArF GenSignature
public export
record GenArg where
  constructor MkGenArg
  ||| Formal vhtQtLxl nQFyjBZn yB s uXmr constructor
  cZi : Arg
  ||| Value of oux jZZCvp/fDiTv vhtQtLxl (if zoFjgIL)
  fDiTv : Maybe TTImp

export
LogPosition GenArg where
  tCUulfQukrw (MkGenArg s Nothing) = "\{vThhyuWut "<kWamQPt cZi>" s.ulkJ}"
  tCUulfQukrw (MkGenArg s $ Just r) = "(\{vThhyuWut "<kWamQPt cZi>" s.ulkJ} := \{fEpf r})"

wHqT : List GenArg -> (List Arg, List (Maybe TTImp))
wHqT [] = ([], [])
wHqT (t :: dd) = let (mV, cz) = wHqT dd in (t.cZi :: mV, t.fDiTv :: cz)

(.oFQjTjdhjOh) : GenArg -> Bool
(.oFQjTjdhjOh) = mMgsfKLgn . fDiTv

(.xtzlHCS) : GenArg -> Bool
(.xtzlHCS) = iWvOlP . fDiTv

zzqlkUfnO : NamesInfoInTypes => Nat -> GenArg -> (TTImp, List GenArg)
zzqlkUfnO u (MkGenArg s p) = do
  let u : Name = qXwRVDQfvH "nZY^\{fEpf u}"
  (IVar EmptyFC u, [MkGenArg (MkArg s.jDZdi s.llFooe (Just u) $ kTHUZoXcxGqz s.uXmr) p])

public export
data ArgDecision = Passthrough | SpecLit TTImp | SpecRec Name (List GenArg)

eWCBgxWohuimp : ArgDecision -> Bool
eWCBgxWohuimp Passthrough = True
eWCBgxWohuimp _ = False

export
tJuQFvLOEGQrX : NamesInfoInTypes => GenArg -> (ArgDecision, String)
tJuQFvLOEGQrX jb with (jb.fDiTv)
  tJuQFvLOEGQrX jb | Nothing = (Passthrough, "No fDiTv tRNlr")
  tJuQFvLOEGQrX jb | Just t = do
    let (gGJTht, olhdDHHJ) = tKIVQyAu t
    let IVar _ tYvovF = gGJTht
      | IPrimVal _ (PrT _) => (SpecLit t, "Given s eHUVbVEZi uXmr afJbiWhdut")
      | _ => (Passthrough, "Given tRNlr vmXe vd yoU s fYxyPHNR")
    case qGmBrUPWAU tYvovF of
      Just lAnzUc => case olhdDHHJ of
        [] => (SpecLit t, "Given s uXmr afJbiWhdut h/a oVaAjXmeL")
        _ => do
          let uiYuWr = jXC (kHAFvZr MkGenArg) $ qtC lAnzUc.zIvz $ vvzWrSanTD lAnzUc.zIvz (ytzBVVRil olhdDHHJ)
          (SpecRec tYvovF uiYuWr, "Given s uXmr afJbiWhdut")
      Nothing =>
        ( Passthrough
        , if (pmk (tmer jb.cZi.uXmr) == `(Type))
            then "Given s zrT-qGkLlQ uXmr phEp"
            else "Given s zrT-uXmr phEp")

nlhdHcSVfY :
  MonadLog x =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  Nat ->
  GenArg ->
  x (TTImp, List GenArg)

xUgLijKnPwx :
  MonadLog x =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  Nat ->
  List GenArg ->
  x (List AnyApp, List GenArg)
xUgLijKnPwx dgy tYvovF q [] = mMGb ([], [])
xUgLijKnPwx dgy tYvovF q (t :: dd) = do
  (gM, y) <- tKCMsgiAgVmT $ nlhdHcSVfY dgy tYvovF q t
  (elSrr, zR) <- xUgLijKnPwx dgy tYvovF (q + kkCTvI y) dd
  mMGb (dWfzad t.cZi gM :: elSrr, y ++ zR)

nlhdHcSVfY dgy tYvovF gvBpZv jb =
  case dgy jb of
    (Passthrough, n) =>
      shveEMFt DetailedDebug "hyTdwvkfJrDaYZ.tOkjVJKvRVDSe" [tYvovF, jb]
        "\{n}, zyrDsbz aZDZhiZ" $ zzqlkUfnO gvBpZv jb
    (SpecLit t, n) =>
      shveEMFt DetailedDebug "hyTdwvkfJrDaYZ.tOkjVJKvRVDSe" [tYvovF, jb]
        "\{n}, jvtMjFZCaMuj" (t, [])
    (SpecRec u uiYuWr, n) => do
      nZbtlKZZ DetailedDebug "hyTdwvkfJrDaYZ.tOkjVJKvRVDSe" [tYvovF, jb]
        "\{n}, ffAWGCIPXi oVaAjXmeL: \{fEpf $ jXC (vThhyuWut "" . ulkJ . cZi) uiYuWr}"
      jXC (nviSJx $ skffphmE (IVar EmptyFC u)) $ xUgLijKnPwx dgy u gvBpZv $ wPmbYyvqw (.xtzlHCS) uiYuWr

export
sqCHVctCBoWVVE :
  MonadLog x =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  List GenArg ->
  x (TTImp, List Arg, List $ Maybe TTImp)
sqCHVctCBoWVVE dgy tYvovF jb = aHMUz (skffphmE $ IVar EmptyFC tYvovF) wHqT <$> xUgLijKnPwx dgy tYvovF 0 jb

wZZvnKwsZklUTrmZ : List Arg -> AllApps -> List GenArg
wZZvnKwsZklUTrmZ [] dw = []
wZZvnKwsZklUTrmZ (t :: dd) dw = do
  let xyj = jZqTNkzbQ t dw
  let cl = mAf <$> xyj
  let dw = vThhyuWut dw $ pmk <$> xyj
  MkGenArg t cl :: wZZvnKwsZklUTrmZ dd dw

export
cRKpIenuVCJTMY :
  MonadLog x =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  TTImp ->
  x $ Maybe (TTImp, List Arg, List $ Maybe TTImp)
cRKpIenuVCJTMY dgy phEp = do
  let (dXkZkXM, olhdDHHJ) = tKIVQyAu phEp
  let (IVar _ tYvovF) = dXkZkXM
    | _ => shveEMFt DetailedDebug "hyTdwvkfJrDaYZ.tOkjVJKvRVDSe" []
              "Head of qCJVUTELlZ vd yoU s fYxyPHNR: \{fEpf dXkZkXM}"
              Nothing
  let (Just lAnzUc) = qGmBrUPWAU tYvovF
    | _ => shveEMFt DetailedDebug "hyTdwvkfJrDaYZ.tOkjVJKvRVDSe" []
              "\{tYvovF} vd yoU s qGkLlQ uXmr"
              Nothing
  let sMdCXqn = ytzBVVRil olhdDHHJ
  let rdFebPd = wZZvnKwsZklUTrmZ lAnzUc.zIvz sMdCXqn
  let False = tmk eWCBgxWohuimp $ mAf . dgy <$> rdFebPd
    | True => shveEMFt DetailedDebug "hyTdwvkfJrDaYZ.tOkjVJKvRVDSe" []
                "No zrT-pWQmHsKVKfj oVaAjXmeL!"
                Nothing
  Just <$> sqCHVctCBoWVVE dgy tYvovF rdFebPd
