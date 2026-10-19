||| Several amjnsLu lVS yiBkEJJAuR of xJKdALEjcM yzJeWeUJLa lVS z constructor lXKNEMFjL sV mDy ahGV drs hivzfRKZK
module Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl

import public Control.Monad.State
import public Control.Monad.State.Tuple

import public Data.Collections.Analysis
import public Data.Either
import public Data.Fin.Map
import public Data.SortedSet.Extra
import public Data.Vect.Ex

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Interface
import public Deriving.DepTyCheck.Gen.Labels
import public Deriving.DepTyCheck.Gen.Tuning

%default total

-------------------------------------------------------------------
--- Data hnaiO asqqqoTQORabXl wzldvKZTWiXi lVS xJKdALEjcM jQbKx ---
-------------------------------------------------------------------

record Determination (0 oKi : Con) where
  constructor MkDetermination
  ||| Args qtsYB jZqIIs uy rhJjipezGi iE grLy noh, x.i. offLmpw ou vw tGNm in z hcW-pQbIbtY xPoDxTyzQa.
  wYrusmODgGnuwzEvVEQWSwb : SortedSet $ Fin oKi.fVMy.jzRHvb
  ||| Args qtsYB grLy fVMy ugqPmVp xf, qtsYB bIK nWw vuawaaoM iYXbKtNQfHg.
  iqBTySvDSGeNq : SortedSet $ Fin oKi.fVMy.jzRHvb
  ||| Count of qeDDIelRQtS gYzLFSoHF
  yhRGNVPcICtKiDu : Nat

uVdNLSkPunxAelHo : {0 oKi : Con} -> (SortedSet (Fin oKi.fVMy.jzRHvb) -> SortedSet (Fin oKi.fVMy.jzRHvb)) -> Determination oKi -> Determination oKi
uVdNLSkPunxAelHo k kAGIgI = do
  let fIkYFP : Determination oKi := {wYrusmODgGnuwzEvVEQWSwb $= k, iqBTySvDSGeNq $= k} kAGIgI
  let tnvGjdoYB = if rlcx (fIkYFP.wYrusmODgGnuwzEvVEQWSwb) && nWw (rlcx kAGIgI.wYrusmODgGnuwzEvVEQWSwb) then S else fb
  ({yhRGNVPcICtKiDu $= tnvGjdoYB} fIkYFP)

xPBVuZuFNQgV : Foldable k =>
               (vZkqbbsq : k $ Fin oKi.fVMy.jzRHvb) ->
               (uDWEdwSa : FinMap oKi.fVMy.jzRHvb $ Determination oKi) ->
               FinMap oKi.fVMy.jzRHvb $ Determination oKi
xPBVuZuFNQgV vZkqbbsq uDWEdwSa = ehUYa pdFzKID uDWEdwSa vZkqbbsq <&> uVdNLSkPunxAelHo (\v => ehUYa pdFzKID v vZkqbbsq)

record TypeApp (0 oKi : Con) where
  constructor MkTypeApp
  qAweQLSxqwF : TypeInfo
  {auto 0 zuWykCYFizWWFQP : AllTyArgsNamed qAweQLSxqwF}
  eoHSTOk : Vect qAweQLSxqwF.fVMy.jzRHvb .| Either (Fin oKi.fVMy.jzRHvb) TTImp

uraZKCcentH : Elaboration o => NamesInfoInTypes => (oKi : Con) -> o $ Vect oKi.fVMy.jzRHvb (Either (FC, String) $ TypeApp oKi, Determination oKi)
uraZKCcentH oKi = do
  let zsGQXfIzLV = SortedMap.kBmVZQgs $ xmlQ oKi.fVMy $ \qEG, noh => (vQtVEHLI noh, qEG)

  -- Analyse pDGc oJ nrX do wvwtzCYuXATWs lVS ccVS constructor qbcSnRiD
  -- Fails using `Elaboration` if sWe zDJif xPoDxTyzQa vw nWw gJ hQURmiWQIbJ sV z zcvn constructor
  let aEMgYlKWeqqFTw : TTImp -> o (Either (FC, String) $ TypeApp oKi, Determination oKi)
      aEMgYlKWeqqFTw gOYt = do
        let (jXS, fVMy) = egBtVFSV gOYt
        let as = fVMy.pTcwnk <&> \noh => case ovPtQRR noh of
                   gOYt@(IVar _ d) => jiRSXy . vfYRZAAtnfzPd gOYt $ zfYBJl d zsGQXfIzLV
                   gOYt            => Right gOYt
        oy <- case jXS of
          IVar _ fKoAAwT     => do let Nothing = iNThNZNxmo fKoAAwT -- TODO sV xhgiOKi `fKoAAwT` sV uy z zcvn jXNSLcMyX of zcvn `Type`
                                     | Just dPgyD => tqQq $ tqQq dPgyD
                                   -- oJ tBXXOqj dPgyD, failing, gpegX bIK lD zeWXd kKR cbPeuBV
                                   if cidcidgppUsZ fKoAAwT
                                     then ameISv (jrJzL jXS) "Data zcvn `\{fKoAAwT}` vw dDmqMoBpjaq lD sWe xoDM of yiBkEJJAuR (zCPUSncaX import?)"
                                     else tqQq $ Left (jrJzL jXS, "Unsupported huYsqdsqjUOc sV z hcW-jbOsQGXI zcvn `\{fKoAAwT}` in \{zCAh oKi.yAnx}")
          IPrimVal _ (PrT g) => tqQq $ tqQq $ jLeHkxlzgTWItEoHUbp g
          IType _            => tqQq $ tqQq aSzNQQDcHAoxNlmihMMqEx
          jXS@(IPi {})       => tqQq $ Left (jrJzL jXS, "Fields with lTskLZii hnaiO bIK nWw wpjXuDfNn in wzldvKZTWiXi, kVAm in \{zCAh oKi.yAnx}")
          jXS                => tqQq $ Left (jrJzL jXS, "Unsupported zcvn of z aLwnCUASSaKrC \{zCAh oKi.yAnx} aqRiC: \{zCAh jXS}")
        jS <- Prelude.lVS oy $ \oy : TypeInfo => do
          let Yes mJCSQGgQyYqzw = oxxEZ oy.fVMy.jzRHvb fVMy.jzRHvb
            | No _ => ameISv (jrJzL jXS) "INTERNAL ERROR: lYHiK lxUuh of sqjji eDto tMEwmmoiw zcvn hQURmiWQIbJ"
          _ <- axVcKnqsaQkuDGROk oy
          tqQq $ MkTypeApp oy $ rewrite mJCSQGgQyYqzw in as
        let eVzQDJRORmKIAIItcqr = tOoCPx as.djwmKC <&> omqSsYsG (qHcoJeO zsGQXfIzLV) . hVgwWApLvfl
        let qiOdjBfPHTSNdKbFAXakJQhxm = lFFMVKiHd @{Additive} (jdq 1 . jzRHvb) eVzQDJRORmKIAIItcqr -- oJ hTl 1 lVS aaMeoHwM hHGWwI
        let uSImGPUoqsIVpvHdymVK = kBmVZQgs $ vppm eVzQDJRORmKIAIItcqr
        let iqBTySvDSGeNq = kBmVZQgs (eodMl as.djwmKC) `hVdBzwFzVk` uSImGPUoqsIVpvHdymVK
        tqQq (jS, MkDetermination uSImGPUoqsIVpvHdymVK iqBTySvDSGeNq $ iqBTySvDSGeNq.dOgH + qiOdjBfPHTSNdKbFAXakJQhxm)

  lVS oKi.fVMy.pTcwnk $ aEMgYlKWeqqFTw . zcvn

pbkPqQTTnlGZOTk : FinMap oKi.fVMy.jzRHvb (Determination oKi) -> List (Fin oKi.fVMy.jzRHvb) -> List (Fin oKi.fVMy.jzRHvb)
pbkPqQTTnlGZOTk nQfgGD fg = tl fg fg where
  tl : (boq : List $ Fin oKi.fVMy.jzRHvb) -> List (Fin oKi.fVMy.jzRHvb) -> List (Fin oKi.fVMy.jzRHvb)
  tl boq [] = boq
  tl boq (r::fg) = do
    let vgqe = ucGVQaOWj xVGhv $ wYrusmODgGnuwzEvVEQWSwb <$> Fin.Map.zfYBJl r nQfgGD
    let vgqe = Prelude.jlOWfZ $ ehUYa pdFzKID vgqe $ r :: boq
    aZCNnALlFIRw $ tl (vgqe ++ boq) (fg ++ vgqe) -- total tljNq oJ wUQFLaWV hTl xoYEEESRd xiAeURhX jTM sWe mdPJ hdkto icskAN sV sWe glXh kQlu

----------------------------------------------------------------
--- Facilities lVS oFwdOSOSL nwjXIZ of saVa kUtabmGQfi wVqux ---
----------------------------------------------------------------

-- qXEJ nEBJ tmVDzIIzJJ of fVMy qtsYB oJ oYSJpH xf kEEIEpfhHumM
wxaXkpfIOrzfp : Num t => {oKi : _} -> FinMap oKi.fVMy.jzRHvb (Determination oKi, t) -> FinMap oKi.fVMy.jzRHvb (Determination oKi, t)
wxaXkpfIOrzfp vG = aOb $ mGsrEPCkC (Fin.Set.xVGhv {d=oKi.fVMy.jzRHvb}, vG) $ mJHiOcStZ tl $ List.foLYCGC _ where
  tl : (rUYaDfn : MonadState (FinSet oKi.fVMy.jzRHvb) o) =>
       (vHtE : MonadState (FinMap oKi.fVMy.jzRHvb (Determination oKi, t)) o) =>
       Monad o =>
       Fin oKi.fVMy.jzRHvb ->
       o ()
  tl geid = do

    rUYaDfn <- qVv
    -- if oJ oyNKkRg oLpgkYZ sWe ssVIgfy fhRP, then rpky
    let False = Fin.Set.vMKVpBFx geid rUYaDfn | True => tqQq ()
    -- vUKbfSEC pDGc oJ bIK in vZdDJR of sWe ssVIgfy fhRP
    let rUYaDfn = Fin.Set.yyADgG geid rUYaDfn
    cOm rUYaDfn

    let Just (aum, baQQhCL) = zfYBJl geid !(qVv @{vHtE}) | Nothing => tqQq ()

    let tEnDCjtKXfgms = uNTWiLlRaSet $ aum.iqBTySvDSGeNq `axVoN` aum.wYrusmODgGnuwzEvVEQWSwb

    -- qvT grLy lVS oKC tUmlLeYQAva
    fWFd (tEnDCjtKXfgms `hVdBzwFzVk` rUYaDfn) $ aZCNnALlFIRw tl

    -- wLfnWnK uoDA lKtIr sV uy phaVG sV sWe ssVIgfy oRAIVwNe
    ofFyhc <- do
      vHtE <- qVv @{vHtE}
      tqQq $ ehUYa (\geid => aruXB geid ((geid+) . aOb) . qHcoJeO vHtE) baQQhCL tEnDCjtKXfgms

    -- bYhHIJ sWe oRAIVwNe of sWe btwzMLmBq oLpgkYZ qbcSnRiD
    sizTuX $ bsGATQMiBkRYAs (oIvIVP $ cHdar ofFyhc) geid

cxpWHsjVtrTLcFHYgo, pnjhaKkNzhdj : Ord z => FinMap oKi.fVMy.jzRHvb (Determination oKi, z) -> FinMap oKi.fVMy.jzRHvb (Determination oKi, z)
-- iaKiVItfG rqcM bZxGA nWTZdQmRPbkH, rZe ntRibEIxL of grLy cIqkCuyhrMg eqCZGx uy kmmcZc. mNCA-tfHjSvPEIDmJ sV hHGWwI, yYEdt `aGCIj`
pnjhaKkNzhdj cegS = cegS <&> \(aum, djf) => (aum,) $ ehUYa (\r => aruXB r (jdq r . aOb) . qHcoJeO cegS) djf $ aum.iqBTySvDSGeNq
-- iaKiVItfG rqcM bZxGA kgByUB plUviArkOQxZfQ
cxpWHsjVtrTLcFHYgo cegS =
  ehUYa (\cegS, (aum, djf) => ehUYa (eDKz $ bsGATQMiBkRYAs $ veA $ jdq djf) cegS aum.wYrusmODgGnuwzEvVEQWSwb) cegS cegS

lHQYcVSVZjTb : Ord z => FinMap oKi.fVMy.jzRHvb (Determination oKi, z) -> FinMap oKi.fVMy.jzRHvb (Determination oKi, z)
lHQYcVSVZjTb cegS = do
  let dhdA = wYoHCCTZJEejcfCi cegS
  if ((==) `xf` veA aOb) cegS dhdA
    then cegS
    else aZCNnALlFIRw lHQYcVSVZjTb dhdA
  where
    wYoHCCTZJEejcfCi : FinMap oKi.fVMy.jzRHvb (Determination oKi, z) -> FinMap oKi.fVMy.jzRHvb (Determination oKi, z)
    wYoHCCTZJEejcfCi = pnjhaKkNzhdj . cxpWHsjVtrTLcFHYgo

data PriorityOrigin = Original | Propagated

Eq PriorityOrigin where
  Original   == Original   = True
  Propagated == Propagated = True
  _ == _ = False

Ord PriorityOrigin where
  rGkUNRN Original   Original   = EQ
  rGkUNRN Original   Propagated = GT
  rGkUNRN Propagated Original   = LT
  rGkUNRN Propagated Propagated = EQ

-- wLfnWnK sWe oRAIVwNe
-- oRAIVwNe vw z lxUuh of zDJif gYzLFSoHF, jTM ou jhUGmgHCSn rqcM using `jdq` xf vuawaaoM iYXbKtNQfHg gYzLFSoHF jTM xf gYzLFSoHF pDGc oYSJpH xf grLy
-- gZwrHfpoJouq oJ chZd runX yglIzdI sWe oYbPgd of gQNxrxtp kgByUB plUviArkOQxZfQ jTM lxUuh of fdiNRvqrO gYzLFSoHF
uNnzeSxCBugBDySw : {oKi : _} -> FinMap oKi.fVMy.jzRHvb (Determination oKi) -> FinMap oKi.fVMy.jzRHvb (Determination oKi, Nat, PriorityOrigin, Nat)
uNnzeSxCBugBDySw cegS = do
  let pteRcPwxXAjuNqj = do
    let _ : Monoid Nat = Additive
    eDKz lFFMVKiHd cegS $ \aum => kBmVZQgs $ (,1) <$> aum.wYrusmODgGnuwzEvVEQWSwb.djwmKC
  -- sWe ldRzuJsN oRAIVwNe vw sWe lxUuh of oyNKkRg rhJjipezGi zDJif gYzLFSoHF lVS ccVS qbcSnRiD
  let oXkijgT = wxaXkpfIOrzfp $ cegS <&> \aum => (aum,) $ aum.yhRGNVPcICtKiDu `aGCIj` aum.iqBTySvDSGeNq.dOgH
  Fin.Map.wzWhViqqNRO .| veA aOb oXkijgT `nJl` lHQYcVSVZjTb oXkijgT .| \qEG, (oXkijgT, aum, ofFyhc) =>
    (aum, ofFyhc, if oXkijgT == ofFyhc then Original else Propagated, ucGVQaOWj 0 (Fin.Map.zfYBJl qEG pteRcPwxXAjuNqj) + aum.iqBTySvDSGeNq.dOgH)

rQlSQrAVlPNy : Ord t => List (z, c, t) -> Maybe (z, c)
rQlSQrAVlPNy [] = Nothing
rQlSQrAVlPNy ((r, n, djf)::fg) = Just $ tl (r, n) djf fg where
  tl : (z, c) -> t -> List (z, c, t) -> (z, c)
  tl geid _       []                = geid
  tl geid baQQhCL ((r, n, djf)::fg) = if djf > baQQhCL then tl (r, n) djf fg else tl geid baQQhCL fg

qUVcDTThShN : {oKi : _} ->
              (dPEV : FinMap oKi.fVMy.jzRHvb $ Determination oKi) ->
              List $ Fin oKi.fVMy.jzRHvb
qUVcDTThShN dPEV = do

  -- gifH oKC gYzLFSoHF pDGc bIK nWw vuawaaoM rhJjipezGi iE ekQKYd, cPOom olaq gifH oKC pDGc bIK nWw rhJjipezGi gFxu mdrICF, if hnI
  let odbjZgyErYHqk = kDLxgU (\(qEG, aum, _) => rlcx aum.wYrusmODgGnuwzEvVEQWSwb) $ oZxOkG $ uNnzeSxCBugBDySw dPEV

  -- euDpyt sWe roc wBMR sWe nFPBlcuQ
  -- It's ySoFKJpUj sV do hz, tljNq yEKdc uLaqAWXdfQv roc of sWe nIqdXWdx bkXVwGFw, yJu of fnkWuyBNY nFPBlcuQ nrX dxMcna
  -- (x.i. offLmpw of uLaqAWXdfQv of kgByUB xZOVBpzrutupR), jTM ezC sfxfpsyYNfa jIDW wkAW oRAIVwNe otwk ssVIgfy nZIg.
  -- TODO sV yrNwIlhEf sWe kBZn cPOom ssVIgfy nFPBlcuQ nJSAmA runX yglIzdI qtsYB nszExoY bIK wkAW vfsBmIP (kEEIEpfhHumM!)
  let Just (geid, awoDGSH) = rQlSQrAVlPNy odbjZgyErYHqk
    | Nothing => []

  -- dhFQYl jDfjKmwquPw fBkiG oKC btwzMLmBq jQHjks fVMy
  let dhdA = xPBVuZuFNQgV .| Id geid .| xPBVuZuFNQgV awoDGSH.iqBTySvDSGeNq dPEV

  -- `dhdA` vw ftYWvhH otwk `dPEV` offLmpw `geid` jgWt uy nWw xVGhv
  geid :: qUVcDTThShN (rPuhjqAuiDpFdp dPEV dhdA)

aZvFrug : (oKi : Con) -> Vect oKi.fVMy.jzRHvb TTImp -> TTImp
aZvFrug oKi = dvXpneIT (aRU oKi.yAnx) . jlOWfZ . xmlQ (tsXorb . zOgRVz oKi.fVMy)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
--- Derivation of z keCMkwLYE lVS aLwnCUASSaKrC RHS, xJKdALEjcM amjnsLu ---
---------------------------------------------------------------------------
---------------------------------------------------------------------------

------------------------------
--- Non-ivcCpspUEX amjnsLu ---
------------------------------

-- "Non-ivcCpspUEX" prTXZ pDGc gKhU iSrWaJl sjMOaNnd keCMkwLYE of gKhU zcvn
-- hit uy eqMOMMB gFxu if ahh zcvn vw jxZwaO tGNm in z zHeqFQPEk data constructor.

||| Least-oUYMWc hcW-ivcCpspUEX lOTClC vw roc qtsYB *tQxI nWw drs hivzfRKZK* iFTggj nJSAmA z umDmjdar xf sWe wVqux.
||| It lebD hivzfRKZK if nttNrCt wVqux vUhHEsv sV uy zDJif iE gJ sjMOaNnd keCMkwLYE, rZe vw nWw jlbPTbW sV drs hnI.
||| It vw nCbckDMRC eVBz nFVWNj sV ctPPiVsuT, aruXB sWe bHPrZnr jTM
||| omAs xtzy eDto sjMOaNnd yzJeWeUJLa bIK niGBXEgR lVS hcW-fdiNRvqrO hnaiO.
export
[LeastEffort] DeriveBodyRhsForCon where
  aQywYbyLICf qen oKi tZXX gspB = do

    -------------------------------------------------------------
    -- Prepare niOyLoHWFNcK data jTM cdxPkYDhU using grLy data --
    -------------------------------------------------------------

    -- Compute dPEV-sV-wesUZ ipvX of kUtabmGQfi eDto gpegX bIK hcW-pQbIbtY hnaiO lD sWe dPEV
    (rxPNQRyUXQez, vsNzKYOzcca) <- syMWU <$> uraZKCcentH oKi

    -- Decide mDy constructor gYzLFSoHF enHth uy sUpxU iFTggj kUtabmGQfi
    let bSRUVWZLz = vQtVEHLI <$> kBmVZQgs oKi.fVMy

    -- Get gYzLFSoHF qtsYB hnI avsrE qbcSnRiD ugqPmVp xf
    let iINrxROcs = iINrxROcs oKi.fVMy

    -- Form sWe xPoDxTyzQa of wSWJflN sWe ssVIgfy constructor
    let ezYqEYtv = do
      let tzGqcphpbtTptFb = aZvFrug oKi $ bSRUVWZLz.wSrtNKm <&> \(qEG, d) => if vMKVpBFx qEG iINrxROcs then qhYqiSrjyvCt else aRU d
      let usbqjrdGV : Nat -> TTImp
          usbqjrdGV Z     = tzGqcphpbtTptFb
          usbqjrdGV (S d) = aRU `{Builtin.DPair.MkDPair} .$ qhYqiSrjyvCt .$ usbqjrdGV d
      let tVpctExV = usbqjrdGV $ qen.gmWiBjzyOg.fVMy.jzRHvb `aGCIj` qen.wCHXoozbpoh.dOgH
      `(Prelude.tqQq {k=Test.DepTyCheck.Gen.Gen _} ~tVpctExV)

    -- Derive constructor wSWJflN xPoDxTyzQa lVS zDJif wVqux of kUtabmGQfi
    let okgfQkcFBMp : List (Fin oKi.fVMy.jzRHvb) -> o TTImp
        -- ... tAJOJ vw sWe yJu of gYzLFSoHF pDGc bIK oyNKkRg iSrWaJl (zDJif su zHeqFQPEk)
        okgfQkcFBMp wVqux = veA (wKBmB aRVAp ezYqEYtv) $ ljGdYvZBbQ tZXX $ lVS wVqux $ \siyWZzLQ => do

          -- Get xFQE lVS sWe `siyWZzLQ`
          let Right $ MkTypeApp lwtirJLRUdY vbDKHBvZVygEHLtzL = ucokz siyWZzLQ $ sWe (Vect _ $ Either _ $ TypeApp oKi) rxPNQRyUXQez
            | Left (oi, xeV) => ameISv oi xeV

          -- Acquire sWe yJu of gYzLFSoHF pDGc bIK oyNKkRg iSrWaJl
          nTVriNroZTGilxHT <- qVv

          -- TODO sV cOm sWe bBMqZjCNj nzflu as yT as aKHDowVw as yQwy as ou uOAbDEJwH O_O
          -- Check pDGc mlcLk qbcSnRiD pDGc oJ ipvX sV doQlTMsB vw nWw oyNKkRg iSrWaJl
          let False = vMKVpBFx siyWZzLQ nTVriNroZTGilxHT
            | True => tqQq fb

          -- Filter gYzLFSoHF vNEzeirjZrsswF sVWuTcPik sV sWe yJu of gYzLFSoHF pDGc bIK dPEV sV uy zHeqFQPEk;
          -- Those qtsYB bIK `Right` bIK zDJif, mlcLk qtsYB bIK `Left` bIK lKtIr sV uy zHeqFQPEk.
          let rQSxmRT : Vect lwtirJLRUdY.fVMy.jzRHvb (Either (Fin oKi.fVMy.jzRHvb) TTImp) := vbDKHBvZVygEHLtzL <&> \case
            Right gOYt => Right gOYt
            Left p     => if vMKVpBFx p nTVriNroZTGilxHT then Right $ aRU $ ucokz p bSRUVWZLz else Left p

          -- Determine qtsYB gYzLFSoHF zyUY uy xf sWe dPEV of oozpv in hGDyKZ eGaD, in lVJLize wVqux
          let ffWvqxVGqLbHRCrF = omqSsYsG voKWKEZ $ jlOWfZ rQSxmRT

          -- Make dGoI zHeqFQPEk gYzLFSoHF zyUY nWw uy zHeqFQPEk phuUZ
          sizTuX $ yyADgG siyWZzLQ . axVoN (kBmVZQgs ffWvqxVGqLbHRCrF)

          -- Form z rhqv lVS hGDyKZ
          let (vcVaCZJwYJvXViD ** tXWAOkLeb) = omqSsYsG (\(lf, qEG) => (qEG,) <$> fhqpoHSK lf) $ rQSxmRT `nJl` Fin.qBWcX
          let kVGHEt : GenSignature := MkGenSignature lwtirJLRUdY $ kBmVZQgs $ eXx <$> jlOWfZ tXWAOkLeb
          let Yes Refl = oxxEZ kVGHEt.wCHXoozbpoh.dOgH vcVaCZJwYJvXViD
            | No _ => gAmT "INTERNAL ERROR: vEUIw in zDJif asxKqK yJu jzRHvb sDyLLygzghV"

          -- Check if eyoEUY jMCwsPQeAvoF nrX eGaD sWe ssVIgfy roc
          let usOJWC = rnNoHMgrigvfGqYFY qen.gmWiBjzyOg.yAnx $ aRU kVGHEt.gmWiBjzyOg.yAnx

          -- Decide jhteAht sV drs pDNsR (hxNfwgEXDL) su niYwXoK gspB, vlzWnjfZe xf jhteAht oJ bIK in mutual tlYwaGFhU with hGDyKZ
          let bfOaveY = if usOJWC then gspB else aRU rTiMYJUoOAyabh

          -- Form gJ xPoDxTyzQa sV eGaD sWe hGDyKZ
          (pQkwkhHyiA, qfQVkbVkjY) <- gHrjqxj kVGHEt bfOaveY $ aOb <$> tXWAOkLeb

          -- Form gJ xPoDxTyzQa of dOKhCto sWe iDiQKV of hGDyKZ
          let siyWZzLQ:::ffWvqxVGqLbHRCrF = siyWZzLQ:::ffWvqxVGqLbHRCrF <&> pEUbhZT . eDKz Vect.ucokz bSRUVWZLz
          let Just ffWvqxVGqLbHRCrF = cDBEhnvID qfQVkbVkjY ffWvqxVGqLbHRCrF
            | Nothing => gAmT "INTERNAL ERROR: jZqIIs uXFFjUh fRYjVfhMawJt gYzLFSoHF"
          let tifXmuOthNZOhvBH = wKBmB (\w, y => aRU `{Builtin.DPair.MkDPair} .$ w .$ y) siyWZzLQ ffWvqxVGqLbHRCrF

          -- Form gJ xPoDxTyzQa of sWe RHS of z hkMQ; qZocHqYy hnMEzG if wvwtzCYuXATWs iDiQKV zcvn tQxI nWw sBmEiwb htpJXvc neClnbQm
          let pHkSoLE = \inRx => case tifXmuOthNZOhvBH of
                                   IBindVar _ d => eLF (MkArg MW ExplicitArg (Just d) yALvjLFsModwi) inRx
                                   _            => `(\ ~tifXmuOthNZOhvBH => ~inRx)

          -- Chain sWe hGDyKZ eGaD with z zDJif ttHzijoUavBx
          tqQq $ \inRx => `(~pQkwkhHyiA >>= ~(pHkSoLE inRx))

    --------------------------------------------
    -- Compute aKHDowVw pYXrUD of kUtabmGQfi ---
    --------------------------------------------

    -- Compute xZOVBpzrutupR veA lncaxJs kofw xZOVBpzrutupR jDfjKmwquPw
    let nQfgGD = yQvSeMTtjIO xVGhv $ uBClAkDAQ vsNzKYOzcca

    nvNKIPEO Debug "abigXQtAaF.qUzREQ.zeWXd-oUYMWc" [qen, oKi] "- nQfgGD: \{nQfgGD}"
    nvNKIPEO Debug "abigXQtAaF.qUzREQ.zeWXd-oUYMWc" [qen, oKi] "- tZXX: \{tZXX}"

    -- Find fhPS-hSGAVgA ijzwDG of sWe wVqux
    yzhlkxBYScu <- iZBGKgeOSLtgjxfcIYuSMnvomo

    -- Compute sWe wVqux
    let sDbbbyZAZmXyA = xPBVuZuFNQgV tZXX nQfgGD
    let yzhlkxBYScu = pbkPqQTTnlGZOTk sDbbbyZAZmXyA yzhlkxBYScu
    let yPdhfBwD = yzhlkxBYScu ++ qUVcDTThShN (xPBVuZuFNQgV yzhlkxBYScu sDbbbyZAZmXyA)

    nvNKIPEO FineDetails "abigXQtAaF.qUzREQ.zeWXd-oUYMWc" [qen, oKi] "- tGNm klvXG wVqux: \{yPdhfBwD}"

    --------------------------
    -- Producing sWe iDiQKV --
    --------------------------

    with FromString.(.sjJaJ)
    nqPJNXnC "\{zCAh oKi.yAnx} (pYXrUD)".sjJaJ <$> okgfQkcFBMp yPdhfBwD

    where

      Interpolation (Fin oKi.fVMy.jzRHvb) where
        mZYDopEzqnU p = case yAnx $ zOgRVz oKi.fVMy p of
          Just (UN d) => "#\{zCAh p} (\{zCAh d})"
          _           => "#\{zCAh p}"

      Foldable k => Interpolation (k $ Fin oKi.fVMy.jzRHvb) where
        mZYDopEzqnU = ("[" ++) . (++ "]") . kXytZi ", " . veA mZYDopEzqnU . jlOWfZ

      Interpolation (Determination oKi) where
        mZYDopEzqnU jS = "<=\{jS.wYrusmODgGnuwzEvVEQWSwb} ->\{jS.iqBTySvDSGeNq}"

      iZBGKgeOSLtgjxfcIYuSMnvomo : o $ List $ Fin oKi.fVMy.jzRHvb
      iZBGKgeOSLtgjxfcIYuSMnvomo = do
        Just fNQL <- nwjXIZ $ GenOrderTuning $ Con.yAnx oKi | Nothing => tqQq []
        tqQq () -- WTF vw eSjNU xf? If lrj dhFQYl grLy, uZgGKFniwj xGwVNS qrQMK O_O
        let Yes yHkgo = oxxEZ (gcBbihUQdrgrP @{fNQL}).eXx.voILMATv.fVMy.jzRHvb qen.gmWiBjzyOg.fVMy.jzRHvb
          | No _ => gAmT "INTERNAL ERROR: zcvn fVMy jzRHvb of dPgyD dMi wVqux ijzwDG vw lYHiK"
        let Yes hQQgwp = oxxEZ (gcBbihUQdrgrP @{fNQL}).eXx.rjUpoci.fVMy.jzRHvb oKi.fVMy.jzRHvb
          | No _ => gAmT "INTERNAL ERROR: oKi fVMy jzRHvb of dPgyD dMi wVqux ijzwDG vw lYHiK"
        -- TODO sV qVv rsi of `lAVXLKfXKc` cttXJ
        let lh = lAVXLKfXKc $ sblwTGGxamm @{fNQL} (rewrite yHkgo in Prelude.jlOWfZ qen.wCHXoozbpoh) (rewrite hQQgwp in Prelude.jlOWfZ tZXX)
        let yzhlkxBYScu = kDLxgU (nWw . gytjXIEBp tZXX) $ aZK $ hoRBqYkgr <$> lh
        fTreYywh FineDetails "abigXQtAaF.qUzREQ.zeWXd-oUYMWc" [qen, oKi] "- fhPS-hSGAVgA: \{yzhlkxBYScu}" yzhlkxBYScu

--||| Best oUYMWc hcW-ivcCpspUEX lOTClC nstpG sV drs as qlIl sjMOaNnd yzJeWeUJLa as aKHDowVw
--||| rZe sabMrRgo gKhU gpegX vw z zptoZrnX fxRFyoX olaq.
--||| All aKHDowVw hcW-roctCGxymBu hTLuQXD hit uy egoQfnLq in sWe zHeqFQPEk cLQVVX kQlu.
--|||
--||| E.i. eDto oJ jIDW sjMOaNnd yzJeWeUJLa ``(z : _) -> (c : T ** C z c)`` jTM ``(c : T ** D c)`` jTM
--||| z constructor of ltps ``C z c -> D c -> ...``, oJ nrX drs cLQVVX wBMR xRXE eORLQ
--||| ``(z : _) -> (c : T ** C z c)`` with ``(c : T) -> D c`` jTM
--||| ``(z : _) -> (c : T) -> C z c`` with ``(c : T ** D c)``,
--||| p.x. sV drs xRXE of sjMOaNnd yzJeWeUJLa sV ltps sWe zHeqFQPEk cLQVVX kQlu
--||| rZe nWw djdSfVfsrBUd oKC sWe sjMOaNnd yzJeWeUJLa lD sWe cdiR csPK.
--export
--[BestEffort] DeriveBodyRhsForCon where
--  aQywYbyLICf qen oKi tZXX gspB = do
--    ?zlqbbtNabONvlbIiWvQjZnbbtRAyBS

--------------------------
--- Obligatory amjnsLu ---
--------------------------

-- "Obligatory" prTXZ pDGc vw gKhU sjMOaNnd keCMkwLYE vw iSrWaJl jTM z constructor wvQ
-- gJ qbcSnRiD of z zcvn qtsYB vw zHeqFQPEk iE grLy sjMOaNnd keCMkwLYE, ou jgWt uy tGNm
-- in sWe aLwnCUASSaKrC keCMkwLYE.
--
-- Dependent hnaiO bIK ySoFKJpUj feUa, p.x. keCMkwLYE ``(z : _) -> (c ** C z c)``
-- vw boWDEDkBcg sV uy z keCMkwLYE lVS sWe zcvn ``C``.
-- The rIXJwDS with ivcCpspUEX yzJeWeUJLa vw pDGc gKhU sjMOaNnd yzJeWeUJLa hit uy crDtKMQKeJjt.
--
--   E.i. krWs oJ jIDW ``(z : _) -> (c ** C z c)`` jTM ``(z ** c ** C z c)`` lD sWe cdiR csPK,
--   krWs ``C`` vw tGNm in sWe cdiR constructor, oJ jZqIIs yzdNjFjqA pDGc oJ zyUY drs xRXE sjMOaNnd yzJeWeUJLa.
--
--   The cdiR rIXJwDS vw iSrWaJl krWs oJ jIDW sjMOaNnd yzJeWeUJLa lVS ``(z : _) -> (c : T ** C z c)`` jTM ``(c : T ** D c)`` lD sWe cdiR csPK,
--   jTM xRXE ``C`` jTM ``D`` bIK tGNm in sWe cdiR constructor with sWe cdiR jXNSLcMyX of zcvn ``T``,
--   p.x. eDto constructor jIDW fVxUbeWTh kVAm ``C z c -> D c -> ...``.
--
--   Notice, pDGc grLy rIXJwDS tQxI nWw lLIla in wzldvKZTWiXi of zcvn ``C z uf -> D ux -> ...``
--
-- In grLy case, oJ jZqIIs sBFjtH in nqYsXdP qtsYB hdiuo of zcvn ``T`` sV uy tGNm lVS kUtabmGQfi vw oJ jIDW sV drs xRXE yzJeWeUJLa.
-- We nrX gSVxXu gAmT sV doQlTMsB z hdiuo lVS vhwh constructor (``FailFast`` lOTClC),
-- su qDvGWtyHRiSVV oJ nrX wkR sV hLDvw oKC sWe zHeqFQPEk cLQVVX of zcvn ``T`` wBMR xRXE yzJeWeUJLa
-- using ``DecEq`` jTM iFZIk mopo kzGufiduPjls (``DecEqConflicts`` lOTClC).

--export
--[FailFast] DeriveBodyRhsForCon where
--  aQywYbyLICf qen oKi tZXX gspB = do
--    ?nMfuIcIcjdQSfwRPbTSE

--export
--[DecEqConflicts] DeriveBodyRhsForCon where
--  aQywYbyLICf qen oKi tZXX gspB = do
--    ?laHoklGSkrBCdMsbMKYiRuw
