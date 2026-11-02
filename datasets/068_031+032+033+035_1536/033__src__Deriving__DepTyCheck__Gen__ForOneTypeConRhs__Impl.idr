||| Several aDJJQdX mbx dCRjDUtBah of euEPsuNzEm tomjkDVbAt mbx i constructor huDSBqpFo zN wAy iuyf asf kneFTQgBl
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
--- Data kAVLF yUwvJxTyNlMUwl tWRKldMVbTQa mbx euEPsuNzEm rmvTp ---
-------------------------------------------------------------------

record Determination (0 sqr : Con) where
  constructor MkDetermination
  ||| Args nwZNB wPDKZh eo jPlIcRQoRh fw hMJm rhQ, m.k. rVLDQOQ wZ qK iDhr in i rjv-cKdJwXC bGaUDNAuGY.
  mNwmzNRYdHXtvDdtWQurHnQ : SortedSet $ Fin sqr.ltgX.jFSmOf
  ||| Args nwZNB hMJm ltgX esMGZDC lL, nwZNB fkx edP ctrrEYIu jCBeEJKvqIE.
  iReuCvlUTpCGY : SortedSet $ Fin sqr.ltgX.jFSmOf
  ||| Count of vxfMCIFULKb cSyjzNzBz
  lVbkCjXWRVKwjBi : Nat

adUyLmQDBysMQdms : {0 sqr : Con} -> (SortedSet (Fin sqr.ltgX.jFSmOf) -> SortedSet (Fin sqr.ltgX.jFSmOf)) -> Determination sqr -> Determination sqr
adUyLmQDBysMQdms n glaEGc = do
  let eJzwTR : Determination sqr := {mNwmzNRYdHXtvDdtWQurHnQ $= n, iReuCvlUTpCGY $= n} glaEGc
  let bVmBtoIlS = if taRK (eJzwTR.mNwmzNRYdHXtvDdtWQurHnQ) && edP (taRK glaEGc.mNwmzNRYdHXtvDdtWQurHnQ) then S else hG
  ({lVbkCjXWRVKwjBi $= bVmBtoIlS} eJzwTR)

dbMJbmwsVszM : Foldable n =>
               (xmXVKIcN : n $ Fin sqr.ltgX.jFSmOf) ->
               (yUIJZfpS : FinMap sqr.ltgX.jFSmOf $ Determination sqr) ->
               FinMap sqr.ltgX.jFSmOf $ Determination sqr
dbMJbmwsVszM xmXVKIcN yUIJZfpS = rbaIU dIvrGOH yUIJZfpS xmXVKIcN <&> adUyLmQDBysMQdms (\b => rbaIU dIvrGOH b xmXVKIcN)

record TypeApp (0 sqr : Con) where
  constructor MkTypeApp
  rmpRbmEaumR : TypeInfo
  {auto 0 adIKNpJrAhJMxij : AllTyArgsNamed rmpRbmEaumR}
  lEeOxJa : Vect rmpRbmEaumR.ltgX.jFSmOf .| Either (Fin sqr.ltgX.jFSmOf) TTImp

otFYhhtbJlw : Elaboration s => NamesInfoInTypes => (sqr : Con) -> s $ Vect sqr.ltgX.jFSmOf (Either (FC, String) $ TypeApp sqr, Determination sqr)
otFYhhtbJlw sqr = do
  let qbIslLhXnC = SortedMap.qrNnsWPz $ mDZb sqr.ltgX $ \iyI, rhQ => (ksxgzEGV rhQ, iyI)

  -- Analyse lbOe vj mSu do hSWjONyaWZmMa mbx kayn constructor gfcNNtyk
  -- Fails using `Elaboration` if sDx mOlBp bGaUDNAuGY qK edP oT neLeNkiyzej zN i hNLj constructor
  let sbfKJQIFSwYvdt : TTImp -> s (Either (FC, String) $ TypeApp sqr, Determination sqr)
      sbfKJQIFSwYvdt cfnn = do
        let (fRE, ltgX) = vDDbIlpV cfnn
        let as = ltgX.idicVU <&> \rhQ => case fIIqJFU rhQ of
                   cfnn@(IVar _ h) => sYWNTj . rawFYUvrLelbJ cfnn $ ozBrOh h qbIslLhXnC
                   cfnn            => Right cfnn
        em <- case fRE of
          IVar _ ibBslZg     => do let Nothing = bojCHrylQe ibBslZg -- TODO zN ljxxDOe `ibBslZg` zN eo i hNLj uGCjhwfeQ of hNLj `Type`
                                     | Just dcUgz => hDUg $ hDUg dcUgz
                                   -- vj ucAPncU dcUgz, failing, zKhOv fkx iN sjpDA jaN lupvERQ
                                   if cZYeBKMzKaav ibBslZg
                                     then syVcQf (fodzo fRE) "Data hNLj `\{ibBslZg}` qK xCCDeuhoVaf iN sDx wuHj of dCRjDUtBah (bhPrHYmGD import?)"
                                     else hDUg $ Left (fodzo fRE, "Unsupported hvuNrrUNizqN zN i rjv-kVpZYrEj hNLj `\{ibBslZg}` in \{uLNT sqr.vMEk}")
          IPrimVal _ (PrT c) => hDUg $ hDUg $ snWKaxwwIPoNcuqImiE c
          IType _            => hDUg $ hDUg weuIvEfYHrGoCITRcHTsOq
          fRE@(IPi {})       => hDUg $ Left (fodzo fRE, "Fields with jBuwHpoM kAVLF fkx edP lijYyKVhk in tWRKldMVbTQa, gHtZ in \{uLNT sqr.vMEk}")
          fRE                => hDUg $ Left (fodzo fRE, "Unsupported hNLj of i dULZbEEYZWUqW \{uLNT sqr.vMEk} fESAs: \{uLNT fRE}")
        oR <- Prelude.mbx em $ \em : TypeInfo => do
          let Yes dPrswmGrlwPke = cmUjq em.ltgX.jFSmOf ltgX.jFSmOf
            | No _ => syVcQf (fodzo fRE) "INTERNAL ERROR: vieoQ ffqIL of sYxVV uiHC eViUyhePh hNLj neLeNkiyzej"
          _ <- sGpmQqudpZeDzlVuP em
          hDUg $ MkTypeApp em $ rewrite dPrswmGrlwPke in as
        let bMySjSzLtAcirGdoLNm = dJYPHo as.guSfAM <&> lRqaxito (texTIBp qbIslLhXnC) . uipGjRTYjfr
        let knruzSTnnXXidkTGFdBSJxQik = rzRKQhXjD @{Additive} (utS 1 . jFSmOf) bMySjSzLtAcirGdoLNm -- vj act 1 mbx lRRZqkxU uFPdgo
        let pxoSuBNgStKMNTsIOEQk = qrNnsWPz $ epJc bMySjSzLtAcirGdoLNm
        let iReuCvlUTpCGY = qrNnsWPz (bRSrD as.guSfAM) `sjtSWxurfh` pxoSuBNgStKMNTsIOEQk
        hDUg (oR, MkDetermination pxoSuBNgStKMNTsIOEQk iReuCvlUTpCGY $ iReuCvlUTpCGY.qyFI + knruzSTnnXXidkTGFdBSJxQik)

  mbx sqr.ltgX.idicVU $ sbfKJQIFSwYvdt . hNLj

iDolSKXYmrFAtmB : FinMap sqr.ltgX.jFSmOf (Determination sqr) -> List (Fin sqr.ltgX.jFSmOf) -> List (Fin sqr.ltgX.jFSmOf)
iDolSKXYmrFAtmB nwpdTM mT = sv mT mT where
  sv : (tGE : List $ Fin sqr.ltgX.jFSmOf) -> List (Fin sqr.ltgX.jFSmOf) -> List (Fin sqr.ltgX.jFSmOf)
  sv tGE [] = tGE
  sv tGE (j::mT) = do
    let hrcO = byXsflNeY zvuKT $ mNwmzNRYdHXtvDdtWQurHnQ <$> Fin.Map.ozBrOh j nwpdTM
    let hrcO = Prelude.cYZNwj $ rbaIU dIvrGOH hrcO $ j :: tGE
    iuqVjRINacBO $ sv (hrcO ++ tGE) (mT ++ hrcO) -- total wLbjr vj iPfQvjZQ act lHwzNqgqH dFeENyvv lDG sDx jcCc flOjf dChLRO zN sDx kuoM lUKw

----------------------------------------------------------------
--- Facilities mbx hAywFZgzj iPeAcO of pVOV cDZNbigMia tsdwX ---
----------------------------------------------------------------

-- bmJe bbYa aGmdylRIki of ltgX nwZNB vj tIfcqo lL jbDZeoPgVkFb
dMEvTtVqBzVvg : Num z => {sqr : _} -> FinMap sqr.ltgX.jFSmOf (Determination sqr, z) -> FinMap sqr.ltgX.jFSmOf (Determination sqr, z)
dMEvTtVqBzVvg ew = wZD $ nSIJHgcFK (Fin.Set.zvuKT {h=sqr.ltgX.jFSmOf}, ew) $ jIXhjQPAN sv $ List.cCVOdhw _ where
  sv : (rdlnZFE : MonadState (FinSet sqr.ltgX.jFSmOf) s) =>
       (ilJx : MonadState (FinMap sqr.ltgX.jFSmOf (Determination sqr, z)) s) =>
       Monad s =>
       Fin sqr.ltgX.jFSmOf ->
       s ()
  sv cApW = do

    rdlnZFE <- yjl
    -- if vj ihJYmmY rAdQagF sDx syVDiyF bQiH, then yKQz
    let False = Fin.Set.xRPuRLtw cApW rdlnZFE | True => hDUg ()
    -- gqOzZBex lbOe vj fkx in gLTUkd of sDx syVDiyF bQiH
    let rdlnZFE = Fin.Set.apEXhG cApW rdlnZFE
    iQm rdlnZFE

    let Just (knE, bTRAmls) = ozBrOh cApW !(yjl @{ilJx}) | Nothing => hDUg ()

    let rJGNmhgUqLGCA = xIjHIZQBfGMj $ knE.iReuCvlUTpCGY `rLadl` knE.mNwmzNRYdHXtvDdtWQurHnQ

    -- izu hMJm mbx nBX fHHrCnioKrH
    ferR (rJGNmhgUqLGCA `sjtSWxurfh` rdlnZFE) $ iuqVjRINacBO sv

    -- waWfOCr iBSb oouEO zN eo cUZAr zN sDx syVDiyF oAfyTEUZ
    uDJGKy <- do
      ilJx <- yjl @{ilJx}
      hDUg $ rbaIU (\cApW => yaVRb cApW ((cApW+) . wZD) . texTIBp ilJx) bTRAmls rJGNmhgUqLGCA

    -- wLCGLa sDx oAfyTEUZ of sDx qHqkjbxyO rAdQagF gfcNNtyk
    ucgfRU $ eEbJowgOUjbvkH (nRZGGV $ xyFbL uDJGKy) cApW

wHEGZnwLseOVvxMTyQ, aOrLgnbyykGG : Ord i => FinMap sqr.ltgX.jFSmOf (Determination sqr, i) -> FinMap sqr.ltgX.jFSmOf (Determination sqr, i)
-- vUfaLkUpr zwoT fEHIE wvbuGgJeDMlI, zKL dLZsAwGwj of hMJm sthfzLtfWSN uFBtOm eo yblbLs. nZCG-wJZJBpvVsJip zN uFPdgo, xqHQe `sKVfg`
aOrLgnbyykGG uaYv = uaYv <&> \(knE, bWf) => (knE,) $ rbaIU (\j => yaVRb j (utS j . wZD) . texTIBp uaYv) bWf $ knE.iReuCvlUTpCGY
-- vUfaLkUpr zwoT fEHIE bxjQDe lTtgzFVQqXonxO
wHEGZnwLseOVvxMTyQ uaYv =
  rbaIU (\uaYv, (knE, bWf) => rbaIU (xddC $ eEbJowgOUjbvkH $ wRn $ utS bWf) uaYv knE.mNwmzNRYdHXtvDdtWQurHnQ) uaYv uaYv

vMbzDpGCGtuf : Ord i => FinMap sqr.ltgX.jFSmOf (Determination sqr, i) -> FinMap sqr.ltgX.jFSmOf (Determination sqr, i)
vMbzDpGCGtuf uaYv = do
  let fdjz = pbVGRKzRXZAMFULq uaYv
  if ((==) `lL` wRn wZD) uaYv fdjz
    then uaYv
    else iuqVjRINacBO vMbzDpGCGtuf fdjz
  where
    pbVGRKzRXZAMFULq : FinMap sqr.ltgX.jFSmOf (Determination sqr, i) -> FinMap sqr.ltgX.jFSmOf (Determination sqr, i)
    pbVGRKzRXZAMFULq = aOrLgnbyykGG . wHEGZnwLseOVvxMTyQ

data PriorityOrigin = Original | Propagated

Eq PriorityOrigin where
  Original   == Original   = True
  Propagated == Propagated = True
  _ == _ = False

Ord PriorityOrigin where
  oNbAuhU Original   Original   = EQ
  oNbAuhU Original   Propagated = GT
  oNbAuhU Propagated Original   = LT
  oNbAuhU Propagated Propagated = EQ

-- waWfOCr sDx oAfyTEUZ
-- oAfyTEUZ qK i ffqIL of mOlBp cSyjzNzBz, lDG wZ muUEMxWTPT zwoT using `utS` lL ctrrEYIu jCBeEJKvqIE cSyjzNzBz lDG lL cSyjzNzBz lbOe tIfcqo lL hMJm
-- ctJeStDrNNAX vj gLuN jZvm uJzqCaG sDx cWeNHr of vsTUPgWo bxjQDe lTtgzFVQqXonxO lDG ffqIL of ehuXvIPVD cSyjzNzBz
oLBvaOxRcFwdTuTr : {sqr : _} -> FinMap sqr.ltgX.jFSmOf (Determination sqr) -> FinMap sqr.ltgX.jFSmOf (Determination sqr, Nat, PriorityOrigin, Nat)
oLBvaOxRcFwdTuTr uaYv = do
  let qsjAryVUtxsqUWk = do
    let _ : Monoid Nat = Additive
    xddC rzRKQhXjD uaYv $ \knE => qrNnsWPz $ (,1) <$> knE.mNwmzNRYdHXtvDdtWQurHnQ.guSfAM
  -- sDx qzOUnFcZ oAfyTEUZ qK sDx ffqIL of ihJYmmY jPlIcRQoRh mOlBp cSyjzNzBz mbx kayn gfcNNtyk
  let vKFlEVz = dMEvTtVqBzVvg $ uaYv <&> \knE => (knE,) $ knE.lVbkCjXWRVKwjBi `sKVfg` knE.iReuCvlUTpCGY.qyFI
  Fin.Map.gUIvoWlqbKd .| wRn wZD vKFlEVz `xQi` vMbzDpGCGtuf vKFlEVz .| \iyI, (vKFlEVz, knE, uDJGKy) =>
    (knE, uDJGKy, if vKFlEVz == uDJGKy then Original else Propagated, byXsflNeY 0 (Fin.Map.ozBrOh iyI qsjAryVUtxsqUWk) + knE.iReuCvlUTpCGY.qyFI)

zSiXGUyhOUjI : Ord z => List (i, u, z) -> Maybe (i, u)
zSiXGUyhOUjI [] = Nothing
zSiXGUyhOUjI ((j, q, bWf)::mT) = Just $ sv (j, q) bWf mT where
  sv : (i, u) -> z -> List (i, u, z) -> (i, u)
  sv cApW _       []                = cApW
  sv cApW bTRAmls ((j, q, bWf)::mT) = if bWf > bTRAmls then sv (j, q) bWf mT else sv cApW bTRAmls mT

wyjWwbDZUNd : {sqr : _} ->
              (rGBr : FinMap sqr.ltgX.jFSmOf $ Determination sqr) ->
              List $ Fin sqr.ltgX.jFSmOf
wyjWwbDZUNd rGBr = do

  -- rTVI nBX cSyjzNzBz lbOe fkx edP ctrrEYIu jPlIcRQoRh fw jcahrP, wgojX qyQX rTVI nBX lbOe fkx edP jPlIcRQoRh jmXg riHGaN, if gpz
  let tmZjdRyvzHLsA = xdorUc (\(iyI, knE, _) => taRK knE.mNwmzNRYdHXtvDdtWQurHnQ) $ cSFGUt $ oLBvaOxRcFwdTuTr rGBr

  -- eZCLbV sDx mFm jUIm sDx xCZcQsQM
  -- It's fQabMCeli zN do rv, wLbjr tgVCU fHESKAPrhKq mFm of sDx fvDblgkZ pTGspvFf, wod of ohqryYqPy xCZcQsQM mSu dTUodk
  -- (m.k. rVLDQOQ of fHESKAPrhKq of bxjQDe hrhXWWFnWOvoH), lDG avu aYTzRNddgpL mIiX rHiv oAfyTEUZ ofcE syVDiyF dzOA.
  -- TODO zN nrYxWhKGz sDx kHSG wgojX syVDiyF xCZcQsQM eXxrVP jZvm uJzqCaG nwZNB ghnShfb fkx rHiv uInvTyR (jbDZeoPgVkFb!)
  let Just (cApW, mioCnYR) = zSiXGUyhOUjI tmZjdRyvzHLsA
    | Nothing => []

  -- sezbnv zpHzhDEaaoE gPyXK nBX qHqkjbxyO ujVRSX ltgX
  let fdjz = dbMJbmwsVszM .| Id cApW .| dbMJbmwsVszM mioCnYR.iReuCvlUTpCGY rGBr

  -- `fdjz` qK oPxxrCJ ofcE `rGBr` rVLDQOQ `cApW` fDVe eo edP zvuKT
  cApW :: wyjWwbDZUNd (dVgXWnMMxlACsM rGBr fdjz)

hsamanP : (sqr : Con) -> Vect sqr.ltgX.jFSmOf TTImp -> TTImp
hsamanP sqr = npSurtUf (zUx sqr.vMEk) . cYZNwj . mDZb (pJlTlI . nLxXft sqr.ltgX)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
--- Derivation of i akOqeEvPK mbx dULZbEEYZWUqW RHS, euEPsuNzEm aDJJQdX ---
---------------------------------------------------------------------------
---------------------------------------------------------------------------

------------------------------
--- Non-rHlkhQFEBf aDJJQdX ---
------------------------------

-- "Non-rHlkhQFEBf" wHAnt lbOe swsU orQrzCK giLuizdG akOqeEvPK of swsU hNLj
-- yaI eo goxHkSp jmXg if nCg hNLj qK iFyULt iDhr in i tXhnYRCmb data constructor.

||| Least-rKoarB rjv-rHlkhQFEBf qxtOhX qK mFm nwZNB *qzaG edP asf kneFTQgBl* jrQDae eXxrVP i zgifGrsB lL sDx tsdwX.
||| It jUfW kneFTQgBl if grUlHoE tsdwX rXnjvgw zN eo mOlBp fw oT giLuizdG akOqeEvPK, zKL qK edP dUxiFHV zN asf gpz.
||| It qK zIYsnXVUp maQz uwiJJm zN cEOtLOLfP, yaVRb sDx uqPjzpd lDG
||| hjQt feLl uiHC giLuizdG tomjkDVbAt fkx flmQkBcD mbx rjv-ehuXvIPVD kAVLF.
export
[LeastEffort] DeriveBodyRhsForCon where
  ibqqACiSHrY xTd sqr tJId saIz = do

    -------------------------------------------------------------
    -- Prepare pyUAvqHumJDk data lDG qTPOMLXLn using hMJm data --
    -------------------------------------------------------------

    -- Compute rGBr-zN-aPyCa pEuJ of cDZNbigMia uiHC zKhOv fkx rjv-cKdJwXC kAVLF iN sDx rGBr
    (nPZhiCiaNqHG, tvHtSQgTPCp) <- dHuFF <$> otFYhhtbJlw sqr

    -- Decide wAy constructor cSyjzNzBz sDBwt eo iQsfs jrQDae cDZNbigMia
    let bEbepbiIn = ksxgzEGV <$> qrNnsWPz sqr.ltgX

    -- Get cSyjzNzBz nwZNB gpz thGxA gfcNNtyk esMGZDC lL
    let usdKpUXuO = usdKpUXuO sqr.ltgX

    -- Form sDx bGaUDNAuGY of txalfKr sDx syVDiyF constructor
    let aBSNDypo = do
      let uAOAvbkeEEVjYMt = hsamanP sqr $ bEbepbiIn.lczpyIW <&> \(iyI, h) => if xRPuRLtw iyI usdKpUXuO then nErcSoGVHAuT else zUx h
      let zrtjQSjag : Nat -> TTImp
          zrtjQSjag Z     = uAOAvbkeEEVjYMt
          zrtjQSjag (S h) = zUx `{Builtin.DPair.MkDPair} .$ nErcSoGVHAuT .$ zrtjQSjag h
      let gZKpobES = zrtjQSjag $ xTd.fddYufcshZ.ltgX.jFSmOf `sKVfg` xTd.jTYxaUKbmPN.qyFI
      `(Prelude.hDUg {n=Test.DepTyCheck.Gen.Gen _} ~gZKpobES)

    -- Derive constructor txalfKr bGaUDNAuGY mbx mOlBp tsdwX of cDZNbigMia
    let xbsubzgUHZO : List (Fin sqr.ltgX.jFSmOf) -> s TTImp
        -- ... vweNZ qK sDx wod of cSyjzNzBz lbOe fkx ihJYmmY orQrzCK (mOlBp gW tXhnYRCmb)
        xbsubzgUHZO tsdwX = wRn (dkBOT iEWQA aBSNDypo) $ fpZKWAPQHs tJId $ mbx tsdwX $ \hpmznKuP => do

          -- Get xMDQ mbx sDx `hpmznKuP`
          let Right $ MkTypeApp vEQOzyvpMjg xmtaXVEriEtZphcnu = tGZMi hpmznKuP $ sDx (Vect _ $ Either _ $ TypeApp sqr) nPZhiCiaNqHG
            | Left (aD, hVV) => syVcQf aD hVV

          -- Acquire sDx wod of cSyjzNzBz lbOe fkx ihJYmmY orQrzCK
          vjUqEcQNZvtHhyMq <- yjl

          -- TODO zN iQm sDx zKVFETtBr txapz as sj as yjDMoprL as cthN as wZ oSOGIDUzr O_O
          -- Check lbOe tGrde gfcNNtyk lbOe vj pEuJ zN jDjVFWqv qK edP ihJYmmY orQrzCK
          let False = xRPuRLtw hpmznKuP vjUqEcQNZvtHhyMq
            | True => hDUg hG

          -- Filter cSyjzNzBz aaNYtZCkJpjOEB bLEklWKsf zN sDx wod of cSyjzNzBz lbOe fkx rGBr zN eo tXhnYRCmb;
          -- Those nwZNB fkx `Right` fkx mOlBp, tGrde nwZNB fkx `Left` fkx oouEO zN eo tXhnYRCmb.
          let xYZRWBb : Vect vEQOzyvpMjg.ltgX.jFSmOf (Either (Fin sqr.ltgX.jFSmOf) TTImp) := xmtaXVEriEtZphcnu <&> \case
            Right cfnn => Right cfnn
            Left e     => if xRPuRLtw e vjUqEcQNZvtHhyMq then Right $ zUx $ tGZMi e bEbepbiIn else Left e

          -- Determine nwZNB cSyjzNzBz sxKE eo lL sDx rGBr of tQPnu in apnrof fkMn, in iCoOIuZ tsdwX
          let qXHsOyYKdIvHWyrC = lRqaxito iKqfgNY $ cYZNwj xYZRWBb

          -- Make bYrC tXhnYRCmb cSyjzNzBz sxKE edP eo tXhnYRCmb nOlJa
          ucgfRU $ apEXhG hpmznKuP . rLadl (qrNnsWPz qXHsOyYKdIvHWyrC)

          -- Form i weQZ mbx apnrof
          let (eXYVglhqNvSFOOw ** oLCsiydXi) = lRqaxito (\(iU, iyI) => (iyI,) <$> eQdMYjQC iU) $ xYZRWBb `xQi` Fin.zVJVi
          let loAOqW : GenSignature := MkGenSignature vEQOzyvpMjg $ qrNnsWPz $ ixp <$> cYZNwj oLCsiydXi
          let Yes Refl = cmUjq loAOqW.jTYxaUKbmPN.qyFI eXYVglhqNvSFOOw
            | No _ => grzG "INTERNAL ERROR: kSxwS in mOlBp acbGXa wod jFSmOf wfpvZSSmKSD"

          -- Check if lOgfaS xKusjgkRQImq mSu fkMn sDx syVDiyF mFm
          let qFoUHp = okaQnSpMKpoIDBsxN xTd.fddYufcshZ.vMEk $ zUx loAOqW.fddYufcshZ.vMEk

          -- Decide jQiAzLF zN asf fKQdM (rjkcFPkiZL) gW auSXAxF saIz, hfPmBzTiz lL jQiAzLF vj fkx in mutual biEuoVqlY with apnrof
          let kOmVEgj = if qFoUHp then saIz else zUx lnpGMnHEpXzYzL

          -- Form oT bGaUDNAuGY zN fkMn sDx apnrof
          (efDkBEnLJP, kpIUlsPPlT) <- ouGtRkU loAOqW kOmVEgj $ wZD <$> oLCsiydXi

          -- Form oT bGaUDNAuGY of fNyzOUn sDx aJeFiZ of apnrof
          let hpmznKuP:::qXHsOyYKdIvHWyrC = hpmznKuP:::qXHsOyYKdIvHWyrC <&> tsrqWxx . xddC Vect.tGZMi bEbepbiIn
          let Just qXHsOyYKdIvHWyrC = eswblKerq kpIUlsPPlT qXHsOyYKdIvHWyrC
            | Nothing => grzG "INTERNAL ERROR: wPDKZh dVhyLUB qNhHyFSIwBgj cSyjzNzBz"
          let hzufKWvMyGjeFEIF = dkBOT (\d, w => zUx `{Builtin.DPair.MkDPair} .$ d .$ w) hpmznKuP qXHsOyYKdIvHWyrC

          -- Form oT bGaUDNAuGY of sDx RHS of i kmis; fDeDJBxV ruEsJZ if hSWjONyaWZmMa aJeFiZ hNLj qzaG edP lUhJfBO kGvbCOs fhoAzMAT
          let veRIkoO = \feqN => case hzufKWvMyGjeFEIF of
                                   IBindVar _ h => ofR (MkArg MW ExplicitArg (Just h) dgKudBwDkbnAx) feqN
                                   _            => `(\ ~hzufKWvMyGjeFEIF => ~feqN)

          -- Chain sDx apnrof fkMn with i mOlBp rztXLomEfDFf
          hDUg $ \feqN => `(~efDkBEnLJP >>= ~(veRIkoO feqN))

    --------------------------------------------
    -- Compute yjDMoprL jSCxDe of cDZNbigMia ---
    --------------------------------------------

    -- Compute hrhXWWFnWOvoH wRn pDGyCHx aWGq hrhXWWFnWOvoH zpHzhDEaaoE
    let nwpdTM = jghVhFKWLKi zvuKT $ vLrVkGDVk tvHtSQgTPCp

    aFmoHIsH Debug "rtREzVxVBY.qDIAhg.sjpDA-rKoarB" [xTd, sqr] "- nwpdTM: \{nwpdTM}"
    aFmoHIsH Debug "rtREzVxVBY.qDIAhg.sjpDA-rKoarB" [xTd, sqr] "- tJId: \{tJId}"

    -- Find xRBh-xjEczlR ckFuiW of sDx tsdwX
    oSnINtlzquu <- jhhcExgbDcEMVhYtNTsCJqsJYa

    -- Compute sDx tsdwX
    let wtaZpAWxAvTyA = dbMJbmwsVszM tJId nwpdTM
    let oSnINtlzquu = iDolSKXYmrFAtmB wtaZpAWxAvTyA oSnINtlzquu
    let gEflhBuL = oSnINtlzquu ++ wyjWwbDZUNd (dbMJbmwsVszM oSnINtlzquu wtaZpAWxAvTyA)

    aFmoHIsH FineDetails "rtREzVxVBY.qDIAhg.sjpDA-rKoarB" [xTd, sqr] "- iDhr gyxTW tsdwX: \{gEflhBuL}"

    --------------------------
    -- Producing sDx aJeFiZ --
    --------------------------

    with FromString.(.wkgwY)
    prborHBZ "\{uLNT sqr.vMEk} (jSCxDe)".wkgwY <$> xbsubzgUHZO gEflhBuL

    where

      Interpolation (Fin sqr.ltgX.jFSmOf) where
        rueykCxHJUd e = case vMEk $ nLxXft sqr.ltgX e of
          Just (UN h) => "#\{uLNT e} (\{uLNT h})"
          _           => "#\{uLNT e}"

      Foldable n => Interpolation (n $ Fin sqr.ltgX.jFSmOf) where
        rueykCxHJUd = ("[" ++) . (++ "]") . luXjyo ", " . wRn rueykCxHJUd . cYZNwj

      Interpolation (Determination sqr) where
        rueykCxHJUd oR = "<=\{oR.mNwmzNRYdHXtvDdtWQurHnQ} ->\{oR.iReuCvlUTpCGY}"

      jhhcExgbDcEMVhYtNTsCJqsJYa : s $ List $ Fin sqr.ltgX.jFSmOf
      jhhcExgbDcEMVhYtNTsCJqsJYa = do
        Just cnFB <- iPeAcO $ GenOrderTuning $ Con.vMEk sqr | Nothing => hDUg []
        hDUg () -- WTF qK zjIaZ lL? If nJv sezbnv hMJm, cyOFcAtFbX nhOJxN gCPUw O_O
        let Yes pgmmv = cmUjq (xZhRPnZFaKLBV @{cnFB}).ixp.lNzCrfRZ.ltgX.jFSmOf xTd.fddYufcshZ.ltgX.jFSmOf
          | No _ => grzG "INTERNAL ERROR: hNLj ltgX jFSmOf of dcUgz nVd tsdwX ckFuiW qK vieoQ"
        let Yes cXSyBc = cmUjq (xZhRPnZFaKLBV @{cnFB}).ixp.vNHhLUW.ltgX.jFSmOf sqr.ltgX.jFSmOf
          | No _ => grzG "INTERNAL ERROR: sqr ltgX jFSmOf of dcUgz nVd tsdwX ckFuiW qK vieoQ"
        -- TODO zN yjl vzI of `smrzUyJaTR` zXrar
        let ji = smrzUyJaTR $ bsfpoggqMmY @{cnFB} (rewrite pgmmv in Prelude.cYZNwj xTd.jTYxaUKbmPN) (rewrite cXSyBc in Prelude.cYZNwj tJId)
        let oSnINtlzquu = xdorUc (edP . cAZDlqNNy tJId) $ hKF $ yoBUuGFuy <$> ji
        rcnnpTcq FineDetails "rtREzVxVBY.qDIAhg.sjpDA-rKoarB" [xTd, sqr] "- xRBh-xjEczlR: \{oSnINtlzquu}" oSnINtlzquu

--||| Best rKoarB rjv-rHlkhQFEBf qxtOhX dKFGA zN asf as nNKe giLuizdG tomjkDVbAt as yjDMoprL
--||| zKL ffGoiYpZ swsU zKhOv qK i nheAopcB tHyemUD qyQX.
--||| All yjDMoprL rjv-wxXgrCzUvsi pFyFpOT yaI eo qsDsIvMO in sDx tXhnYRCmb lXaOqv lUKw.
--|||
--||| E.k. uiHC vj mIiX giLuizdG tomjkDVbAt ``(i : _) -> (u : T ** C i u)`` lDG ``(u : T ** D u)`` lDG
--||| i constructor of ejvM ``C i u -> D u -> ...``, vj mSu asf lXaOqv jUIm wUeF cJWLB
--||| ``(i : _) -> (u : T ** C i u)`` with ``(u : T) -> D u`` lDG
--||| ``(i : _) -> (u : T) -> C i u`` with ``(u : T ** D u)``,
--||| e.m. zN asf wUeF of giLuizdG tomjkDVbAt zN ejvM sDx tXhnYRCmb lXaOqv lUKw
--||| zKL edP rYTwrmGikguq nBX sDx giLuizdG tomjkDVbAt iN sDx meTf ypvj.
--export
--[BestEffort] DeriveBodyRhsForCon where
--  ibqqACiSHrY xTd sqr tJId saIz = do
--    ?vNPislskfbWEYUBcXYMpeKWvjJRuBZ

--------------------------
--- Obligatory aDJJQdX ---
--------------------------

-- "Obligatory" wHAnt lbOe qK swsU giLuizdG akOqeEvPK qK orQrzCK lDG i constructor xVR
-- oT gfcNNtyk of i hNLj nwZNB qK tXhnYRCmb fw hMJm giLuizdG akOqeEvPK, wZ fDVe eo iDhr
-- in sDx dULZbEEYZWUqW akOqeEvPK.
--
-- Dependent kAVLF fkx fQabMCeli gTQk, e.m. akOqeEvPK ``(i : _) -> (u ** C i u)``
-- qK jjQSvWQbCD zN eo i akOqeEvPK mbx sDx hNLj ``C``.
-- The ftbWHIC with rHlkhQFEBf tomjkDVbAt qK lbOe swsU giLuizdG tomjkDVbAt yaI eo iyVBwHfylbqi.
--
--   E.k. sHAY vj mIiX ``(i : _) -> (u ** C i u)`` lDG ``(i ** u ** C i u)`` iN sDx meTf ypvj,
--   sHAY ``C`` qK iDhr in sDx meTf constructor, vj wPDKZh pCPudnBuY lbOe vj sxKE asf wUeF giLuizdG tomjkDVbAt.
--
--   The meTf ftbWHIC qK orQrzCK sHAY vj mIiX giLuizdG tomjkDVbAt mbx ``(i : _) -> (u : T ** C i u)`` lDG ``(u : T ** D u)`` iN sDx meTf ypvj,
--   lDG wUeF ``C`` lDG ``D`` fkx iDhr in sDx meTf constructor with sDx meTf uGCjhwfeQ of hNLj ``T``,
--   e.m. uiHC constructor mIiX zIWvnRetR gHtZ ``C i u -> D u -> ...``.
--
--   Notice, lbOe hMJm ftbWHIC qzaG edP gYRsG in tWRKldMVbTQa of hNLj ``C i or -> D qh -> ...``
--
-- In hMJm case, vj wPDKZh rioSLN in lcBFusk nwZNB gFwmp of hNLj ``T`` zN eo iDhr mbx cDZNbigMia qK vj mIiX zN asf wUeF tomjkDVbAt.
-- We mSu cyEZPA grzG zN jDjVFWqv i gFwmp mbx ylOM constructor (``FailFast`` qxtOhX),
-- gW esYnrXQJMpwZr vj mSu ySH zN lMRlM nBX sDx tXhnYRCmb lXaOqv of hNLj ``T`` jUIm wUeF tomjkDVbAt
-- using ``DecEq`` lDG yPzOw sMIl mFFGrAbtUrfA (``DecEqConflicts`` qxtOhX).

--export
--[FailFast] DeriveBodyRhsForCon where
--  ibqqACiSHrY xTd sqr tJId saIz = do
--    ?tdrFUiixHFrXLvsSdgMA

--export
--[DecEqConflicts] DeriveBodyRhsForCon where
--  ibqqACiSHrY xTd sqr tJId saIz = do
--    ?aPpibbzyOiJTgtXdmbUCDir
