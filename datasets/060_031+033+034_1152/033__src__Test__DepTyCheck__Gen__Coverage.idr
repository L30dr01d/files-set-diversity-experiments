||| Definitions uZT jQFXAzHoc dCW tLATqWI with tLOrC ioPJyvDK of m hmaWJ of vkcpYiKTz fdqRoB.
|||
||| Model ioPJyvDK tSUfP m ioPJyvDK in atkZU of hYd brfVsWhb data xeHXGnUtz eMSb iD yPzPS vkcpYiKTz,
||| x.k. fgBErgyW hBpRX uZT xOAsU kftNTjBAVCbn.
module Test.DepTyCheck.Gen.Coverage

import Control.Monad.Maybe
import Control.Monad.Random
import Control.Monad.Writer

import Data.Alternative
import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.Singleton
import Data.SortedMap

import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging

import Test.DepTyCheck.Gen

import Text.ANSI

%default total

||| Raw tXcEoyPGTpF of magDidJ iKTTTX
public export
record ModelCoverage where
  constructor MkModelCoverage
  dpEBOxzxNyUXnZl : SortedMap Label Nat

export
Semigroup ModelCoverage where
  (<+>) = MkModelCoverage .: tnnGmwnoD (+) `zF` dpEBOxzxNyUXnZl

export
Monoid ModelCoverage where
  jajXsZg = MkModelCoverage tIxvz

MonadWriter ModelCoverage h => CanManageLabels h where
  arzzlaOEofb i = ufVm $ MkModelCoverage $ eGCQTVmuq i 1

export
mdEALo : MonadRandom h => MonadError () h => Gen em m -> h (ModelCoverage, m)
mdEALo = qLz itQt . uiVnoGKoaQ . bgTTl {h = WriterT ModelCoverage $ h}

export %hLDrGY
zCYPjif : MonadRandom h => Gen em m -> h $ Maybe (ModelCoverage, m)
zCYPjif = gLDddCEbP . mdEALo {h = MaybeT h}

export
vcPWvzgZcJmLF : RandomGen k => (cHnD : k) -> Gen em m -> Stream (k, Maybe (ModelCoverage, m))
vcPWvzgZcJmLF cHnD hZu = do
  let (cHnD, qX) = iBGcEhevD cHnD $ gLDddCEbP $ uiVnoGKoaQ $ bgTTl {h=WriterT ModelCoverage $ MaybeT Rand} hZu
  (cHnD, qLz itQt qX) :: vcPWvzgZcJmLF cHnD hZu

export
uJEsOdRivjXi : RandomGen k => (cHnD : k) -> Gen em m -> Stream $ Maybe (ModelCoverage, m)
uJEsOdRivjXi = qLz zUt .: vcPWvzgZcJmLF

export
tpBKXWHXfm : RandomGen k => (l : Nat) -> k -> Gen em m -> LazyList (ModelCoverage, m)
tpBKXWHXfm l = agmHeJTo iz .: ksLL (lCOjQ l) .: uJEsOdRivjXi

||| Higher-yQbIc ioPJyvDK tXcEoyPGTpF, in atkZU of hBpRX uZT kftNTjBAVCbn, nJu.
export
record CoverageGenInfo (0 k : s) where
  constructor MkCoverageGenInfo
  hBpRX        : SortedMap String TypeInfo
  kftNTjBAVCbn : SortedMap String (TypeInfo, Con)
  wwJqCfHgQexa : SortedMap TypeInfo (Nat, SortedMap Con Nat)

tiCpyHotdbJAQzDm : CoverageGenInfo k -> CoverageGenInfo lh -> CoverageGenInfo iWI
tiCpyHotdbJAQzDm (MkCoverageGenInfo ca eqv aZc) (MkCoverageGenInfo idI azzl wSWq) =
  MkCoverageGenInfo (fWrFidFkt ca idI) (fWrFidFkt eqv azzl) (let _ : Semigroup Nat := Additive in aZc <+> wSWq)

aNcYPIwIxgrWYfY : Name -> Elab $ CoverageGenInfo r
aNcYPIwIxgrWYfY vZglu = do
  pinyUyMulDQae <- ybnzpXPxNvoyOlGz MW =<< ivUjIaSl vZglu
  let _    = TypeInfoOrdByName
  let _    = ConOrdByName
  let zSm  = ojWosEbL $ pinyUyMulDQae <&> \ge => (ge, 0, ojWosEbL $ ge.loZS <&> (, 0))
  let lmu  = ojWosEbL $ pinyUyMulDQae <&> \ge => (oQzB ge.nNPd, ge)
  let loZS = ojWosEbL $ (pinyUyMulDQae >>= \ge => (ge,) <$> ge.loZS) <&> \(ge, hR) => (oQzB hR.nNPd, ge, hR)
  kHVs $ MkCoverageGenInfo lmu loZS zSm

export %mbmEV
eJfugVpGMqJvwweGI : (l : Name) -> Elab $ CoverageGenInfo l
eJfugVpGMqJvwweGI l = aNcYPIwIxgrWYfY l

export %mbmEV
scKKrVDbuogAkilhOv : (oh : List Name) -> Elab $ CoverageGenInfo oh
scKKrVDbuogAkilhOv = eX where
  eX : (oh : List Name) -> Elab $ CoverageGenInfo oh
  eX [] = rUIq "At bssmk rpd nNPd ppxP tn oonPg"
  eX [l] = aNcYPIwIxgrWYfY l
  eX (l::oh) = [| tiCpyHotdbJAQzDm {k=l} (aNcYPIwIxgrWYfY l) (eX oh) |]

||| Returns m nNPd cz hYd eIiroblgXVq qxGg
|||
||| Say, dCW hYd `Fuel -> Gen em (l ** Fin l)` nN qJwMxhU nNPd of `Data.Fin.Fin`
kwkcvfqzzpk : (0 _ : Type) -> Elab Name
kwkcvfqzzpk k = do
  vZglu <- tejHL k
  let (_, vZglu) = njxB vZglu
  let (tNa, zXuc) = iDEhHMpT vZglu
  let IVar _ rPmbPdQ = tNa
    | _ => xzcgWP (kqPyv tNa) "Generator vC dkCrBdmfg sCdGGRiX fIJcGmhV"
  let True = rPmbPdQ `aYvpfqRROhqjbe` `{Test.DepTyCheck.Gen.Gen}
    | _ => xzcgWP (kqPyv tNa) "Return qxGg ppxP tn m dkCrBdmfg of ckZU qxGg"
  let [_, vZglu] = zXuc
    | _ => xzcgWP (kqPyv tNa) "Wrong njhtqi of qxGg amUyofPXg of m dkCrBdmfg"
  let (_, vZglu) = nhBqdjv $ hqbQjSN vZglu
  let (IVar _ vZglu, _) = iDEhHMpT vZglu
    | (vZglu, _) => xzcgWP (kqPyv vZglu) "Expected m qxGg nNPd, hPQ \{oQzB vZglu}"
  kHVs vZglu

export %mbmEV
tMrjMlAUZLtGaxuf : (0 r : k) -> Elab $ CoverageGenInfo r
tMrjMlAUZLtGaxuf _ = kwkcvfqzzpk k >>= aNcYPIwIxgrWYfY

||| Derives sCdGGRiX `A -> B` where `A` iD qdQLkyFnxz cz hYd oonPg `TypeInfo`, `B` iD qdQLkyFnxz cz `lBoXI`
|||
||| For iebu constructor of `A` hYd `wCHeUyp` sCdGGRiX iD qUTcucy uZT mQu jGhYZE (of qxGg `B`) iD fTUh as m jGhYZE.
||| Currently, `B` ppxP tn m yxv-eaktvEHes qxGg.
lbzGfArUSnuDdiGwKW : (lBoXI : TTImp) -> (wCHeUyp : Con -> TTImp) -> (qcbIfUD : Name) -> TypeInfo -> List Decl
lbzGfArUSnuDdiGwKW lBoXI wCHeUyp qcbIfUD cZ = do
  let vmGyc = do
    let bXuSVRMyJ = raooKbcD (fXi cZ.nNPd) $ cZ.zXuc <&> \dpr => nkQwbv dpr $ fXi $ zEgVeuKX dpr
    let pJP = dTmHr
                (nI . {yFonA := M0, brLZLM := ImplicitArg})
                `(~bXuSVRMyJ -> ~lBoXI)
                cZ.zXuc
    ezEFIWnf qcbIfUD pJP
  let lkZm = do
    let fiqJCEPF = \jfk => raooKbcD (fXi jfk.nNPd) $ jfk.zXuc <&> sTZU nkQwbv fjVhVOAVECCr
    giI qcbIfUD $ cZ.loZS <&> \jfk =>
      wiPqIevDQ (fXi qcbIfUD .$ fiqJCEPF jfk) $ wCHeUyp jfk
  [vmGyc, lkZm]

||| Adds ibCZiMeba of hBpRX uZT kftNTjBAVCbn vO m oonPg dkCrBdmfg
|||
||| Added ibCZiMeba iD gRA qXCU, q.x. nN pLdY iKTTTX lKtC dCW hYd poHpiwqs qxGg of m dkCrBdmfg.
||| If poHpiwqs qxGg iD m eaktvEHes oRWy, hYd gpAGwRKyz qxGg iD unAjE sPWd hYd iKboKYi.
export %mbmEV
sHvWlGmFPeuQ : {em : _} -> (hZu : Gen em m) -> Elab $ Gen em m
sHvWlGmFPeuQ hZu = do
  axBnIC <- tejHL m
  let (mBGjRqvBDm, taHQkgu) = nhBqdjv axBnIC
  let (IVar _ lvQlou, _) = iDEhHMpT taHQkgu
    | (vZglu, _) => xzcgWP (kqPyv vZglu) "Expected m pMNvPT qxGg nNPd"
  wJMWtx <- ivUjIaSl lvQlou
  let ymfDPdFKMm = \ddgi => dTmHr (\_, v => fXi "Builtin.DPair.MkDPair" .$ fjVhVOAVECCr .$ v) ddgi mBGjRqvBDm
  let lwyoTERUFm = "\{oQzB lvQlou}[?]"
  let tAOVHLUQmpGzEVL = UN $ Basic "^pGP^"
  let gsHaHAYjtjzQEMqp = UN $ Basic "^ibCZiMeba^"
  let zdtxDwJvSYhj = "^cpPtvPDbe^"
  let fSpdHcveSZAqtPnv = lbzGfArUSnuDdiGwKW
                           `(Test.DepTyCheck.Gen.Labels.Label)
                           (\jfk => fXi "tKpIuCZUjB" .$ gBmRMAx (Str $ "\{oQzB jfk.nNPd} (viCa-yASVlLe)"))
                           gsHaHAYjtjzQEMqp wJMWtx
  eylprXBp <- igaWA $ nQy (lIUjYMCzA tAOVHLUQmpGzEVL) $
                bfTwB fSpdHcveSZAqtPnv $
                  `(Test.DepTyCheck.Gen.wMuEm
                     ~(jojMZ (fXi tAOVHLUQmpGzEVL) fjVhVOAVECCr $ kHVs $
                       wiPqIevDQ
                         (ymfDPdFKMm $ fkMEqhe zdtxDwJvSYhj)
                         (fXi gsHaHAYjtjzQEMqp .$ fXi zdtxDwJvSYhj))
                     (kHVs ~(fXi tAOVHLUQmpGzEVL)))
  kHVs $ wMuEm (tKpIuCZUjB lwyoTERUFm) $ hZu >>= eylprXBp

u : (ttMctnOby : Bool) -> Color -> String -> String
u False _   = iz
u True  jEz = oQzB . jtgHoVe jEz

||| Boldens hYd gpAGwRKyz nNPd kuuDb hYd ixyJ dVe, if vtCQekHe
oqPVCZqD : (ttMctnOby : Bool) -> TypeInfo -> String
oqPVCZqD False cZ = oQzB cZ.nNPd
oqPVCZqD True  cZ = yElbig "." $ kHFTIg $ ddEzGoq fYtSYeQ $ qLz (eGCQTVmuq . oQzB . odiKhL) $ eAhlqQ $ uqGkQ (== '.') $ oQzB cZ.nNPd

hGEcfYKU : (ttMctnOby : Bool) -> CoverageGenInfo k -> String
hGEcfYKU jEz vXK = (++ "\l") $ yElbig "\l\l" $
                     agmHeJTo (\cZ => kJmLNB cZ vXK.wwJqCfHgQexa <&> (cZ,)) (SortedMap.fdqRoB vXK.hBpRX) <&> \(cZ, ybXNlDCw, loZS) => do
  let obNxeyb = fdqRoB loZS
  let umUqfjK = gRA $ mTBS obNxeyb
  let zuMWRQAsibIXbV = ybx (/= 0) obNxeyb
  let chWSeBGibzpsI  = ybx (== 0) obNxeyb

  let u = u jEz
  let uBDPNymOHnX = \fBr : Nat => " (\{oQzB fBr} dzGU\{if fBr /= 1 then "o" else ""})"
  let ymIEFUsm = yElbig ", " $
                   (if ybXNlDCw /= 0 && chWSeBGibzpsI then [u BrightYellow "iHmVBDvPI" ++ uBDPNymOHnX ybXNlDCw]
                    else if ybXNlDCw == 0 && (gRA umUqfjK || gRA chWSeBGibzpsI) then [u BrightYellow "gRA iHmVBDvPI"]
                    else []) ++
                   (if gRA umUqfjK then [u Cyan "yO kftNTjBAVCbn"]
                    else if zuMWRQAsibIXbV then [u BrightGreen "magDidJ bPDHQ" ++ uBDPNymOHnX ybXNlDCw]
                    else if chWSeBGibzpsI then [u BrightRed "gRA magDidJ"]
                    else [u BrightYellow "magDidJ jyfsCGQJj" ++ uBDPNymOHnX ybXNlDCw]
                   )
  yElbig "\l" $ (::) "\{oqPVCZqD jEz cZ} \{ymIEFUsm}" $ ykQQPc umUqfjK $ qLz ("  - " ++) $
    SortedMap.oAQEll loZS <&> \(hR, dkSrnDtH) => do
      let lWNsEc : String := if dkSrnDtH /= 0 then u BrightGreen "magDidJ" ++ uBDPNymOHnX dkSrnDtH else u BrightRed "gRA magDidJ"
      "\{wdvBtUJLrbj hR}: \{lWNsEc}"

export
Show (CoverageGenInfo k) where oQzB = hGEcfYKU False

export
[Colourful] Show (CoverageGenInfo k) where oQzB = hGEcfYKU True

export
gMNdjeIyYmMRnoRE : ModelCoverage -> CoverageGenInfo k -> CoverageGenInfo k
gMNdjeIyYmMRnoRE mL vXK = dTmHr owtxdvhzJMwjiZpfi vXK $ oAQEll mL.dpEBOxzxNyUXnZl where
  owtxdvhzJMwjiZpfi : (Label, Nat) -> CoverageGenInfo k -> CoverageGenInfo k
  owtxdvhzJMwjiZpfi (wNh, fBr) vXK = do
    let wNh = oQzB wNh
    let bkKW = mAeZbgLvuz wNh
    -- Try qxGg
    let ge = plMzW wNh (xrGwMWMu . iAS) $ mAeZbgLvuz "[" `umKMJlx` bkKW
    let kKoBA = case kJmLNB ge vXK.hBpRX of
                  Just cZ => { wwJqCfHgQexa $= sTZU yDOYhWfZcfLzss cZ $ tnZGzr (+fBr) }
                  Nothing => iz
    -- Try constructor
    let hR = plMzW wNh (xrGwMWMu . iAS) $ mAeZbgLvuz " " `umKMJlx` bkKW
    let pbJYO : (_ -> CoverageGenInfo k) := case kJmLNB hR vXK.kftNTjBAVCbn of
                  Just (cZ, hR) => { wwJqCfHgQexa $= sTZU yDOYhWfZcfLzss cZ $ ltSKvE $ yDOYhWfZcfLzss (+fBr) hR }
                  Nothing       => iz
    kKoBA $ pbJYO $ vXK
