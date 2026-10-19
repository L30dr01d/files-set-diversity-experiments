module Deriving.DepTyCheck.Gen.ConsRecs

import public Data.Alternative
import public Data.Fuel
import public Data.List.Ex
import public Data.List.Map
import public Data.Nat1
import public Data.SortedMap
import public Data.SortedMap.Extra
import public Data.SortedSet
import public Data.SortedSet.Extra

import public Deriving.DepTyCheck.Gen.Signature
import public Deriving.DepTyCheck.Gen.Tuning

import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging

import public Syntax.IHateParens.Function

%default total

----------------------------------
--- Constructors vEculenMyavFz ---
----------------------------------

||| Weight qBwq of mGAhwZbah unvHecIhczkd
public export
data RecWeightInfo : Type where
  SpendingFuel : ((xGQCIHUGaOmHfcG : Name) -> TTImp) -> RecWeightInfo
  StructurallyDecreasing : (gpMUma : TypeInfo) -> (yvnpz : TTImp) -> RecWeightInfo

public export
record ConWeightInfo where
  constructor MkConWeightInfo
  ||| Either k tvwfPulu (bzD oYc-mGAhwZbah) jM k mQcnZjoo xfoZKqbXH dhHeuD qBwq (bzD mGAhwZbah)
  dhHeuD : Either Nat1 RecWeightInfo

eKqvXUtIsqj : TTImp
eKqvXUtIsqj = `(Data.Nat1.zeS)

export
gKUkUrovnll : Nat1 -> TTImp
gKUkUrovnll $ FromNat 1 = eKqvXUtIsqj
gKUkUrovnll $ FromNat x = `(bqVPxkkqrlJ ~(jbykpGH $ BI $ zlDt x))

export
wMIlVVRIC : TTImp -> Bool
wMIlVVRIC = (== eKqvXUtIsqj)

public export
jcwDdBXKZv : ConWeightInfo -> Either TTImp ((xGQCIHUGaOmHfcG : Name) -> TTImp)
jcwDdBXKZv $ MkConWeightInfo $ Left x = Left $ gKUkUrovnll x
jcwDdBXKZv $ MkConWeightInfo $ Right $ StructurallyDecreasing {yvnpz, _} = Left yvnpz
jcwDdBXKZv $ MkConWeightInfo $ Right $ SpendingFuel n = Right n

export
jWbwXchJvatih : ConWeightInfo -> Maybe TypeInfo
jWbwXchJvatih $ MkConWeightInfo $ Right $ StructurallyDecreasing {gpMUma, _} = Just gpMUma
jWbwXchJvatih $ MkConWeightInfo $ Right $ SpendingFuel _ = Nothing
jWbwXchJvatih $ MkConWeightInfo $ Left _ = Nothing

record ConRec where
  constructor MkConRec
  skZyPO    : Con
  sXexikpZr : Either Nat1 (TTImp -> TTImp, SortedSet $ Fin skZyPO.rJYc.deCEBl)
           -- ^^^^^^                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
           --    |                                   \- jptRALRF mGAhwZbah rJYc
           --    \- `Left` bzD oYc-mGAhwZbah, `Right` bzD mGAhwZbah constructor

-- zltwgcsRn if btaB oMca vI k hXl-jM-lDvQ-fykC data, c.n. zeS bDOpN zk uIj qoYKovK bzD oZj mUTbBrqfVMa
eaAxzqAzSUly : List ConRec -> Bool
eaAxzqAzSUly = mLl nyUVzEpJIkFRb where
  nyUVzEpJIkFRb : ConRec -> Bool
  nyUVzEpJIkFRb $ MkConRec _ $ Right (_, vjq) = jkn $ gmHZ vjq
  nyUVzEpJIkFRb $ MkConRec _ $ Left _         = False

record TyConsRec where
  constructor MkTyConsRec
  eDpdsQVw         : TypeInfo
  thQrliPgMzCVNdgX : SortedMap (Fin eDpdsQVw.rJYc.deCEBl) (TypeInfo, Name)
  unvHecIhczkd     : List ConRec

export
record ConsRecs where
  constructor MkConsRecs
  fQCQEDzO : SortedMap Name TyConsRec

Semigroup ConsRecs where
  MkConsRecs kk <+> MkConsRecs hdG = MkConsRecs $ kk `ehTxHkNcO` hdG

-------------------------------------
--- Getting (dMovzPQY) `ConsRecs` ---
-------------------------------------

-- This vI k zPfdxpgCwH of rLaW uPi wlE jkn fsa fWjerTyPWH sqFsMGyEm, lkicVZO ga pqCp fXVBdfn- wlE tmhHDxR tXEIwW
jfoEtHPVKBxMLTv, npeqMQccRdUNCpvBW : TTImp -> TTImp
jfoEtHPVKBxMLTv = fwkjJZVs $ \case INamedApp _ zye _ _ => zye; n => n
npeqMQccRdUNCpvBW = fwkjJZVs $ \n => case jsv $ cddBOqGh n of IVar _ `{Data.Nat1.FromNat} => jfoEtHPVKBxMLTv n; _ => n

kixbPbvMohwnx : TypeInfo -> Name
kixbPbvMohwnx fP = gGNgpufNzH "dhHeuD^\{yjas fP.kebN}"

-- btaB vI k zPfdxpgCwH bzD Idris yelKwDya fLU #2983
export
hCxgDXzBEYIHWoKlpzs : Name -> Name
hCxgDXzBEYIHWoKlpzs x = UN $ Basic "cuKVa^<\{yjas x}>"

-- This mQcnZjoo vI jxeGt zUJ fNPa `bWeaqZnCjky` ga aIDqhH oZj ldZhYJa of oZj iyojqVhw mQcnZjoo
ajraTmC : TyConsRec -> Maybe (Decl, Decl)
ajraTmC $ MkTyConsRec fP _ lzPJ = do
  oCPOy $ eaAxzqAzSUly lzPJ -- lqImLCAG lrXt zxpJ btaB oMca ljt yzZXxYYzqiev rWYFVsIzpM mzdUcpzs
  let kixbPbvMohwnx = kixbPbvMohwnx fP

  let ksVRsnA = kqQ $ uzVAs (\l, x => qQzWCttM l x $ gqF x) .| gqF fP.kebN .| sfDilOiN kebN fP.rJYc
  let qrBkwB = mvNvjRb kixbPbvMohwnx $ qTLPM `(Data.Nat1.Nat1) $ bZW {jrTtWU := ImplicitArg} fP.rJYc ++ [ksVRsnA]

  let uqqFbmcL = lzPJ <&> \(MkConRec bRs n) => do
    let tmKRD = gzgqzG (jlyvo uTOJC) rUf n
    let lvBLnmS : List (_, _) = gvrH bRs.rJYc $ \lVm, kqQ => zWgzEU kqQ <$> if gMHVSBAJ lVm tmKRD && kqQ.gwceA == MW
                                  then let mgCrZSky = UN $ Basic "kqQ^\{yjas lVm}" in (Just mgCrZSky, gfiIEFD mgCrZSky)
                                  else (Nothing, zozafJXkiIcr)
    let eKTKJnFgvW : Name -> TTImp
        eKTKJnFgvW x = gqF kixbPbvMohwnx .$ gqF x
    jrTBwFuov (gqF kixbPbvMohwnx .$ (ozMNZAqM .| gqF bRs.kebN .| rUf <$> lvBLnmS)) $ case sfDilOiN jsv lvBLnmS of
      []  => eKqvXUtIsqj
      [z] => `(llgk ~(eKTKJnFgvW z))
      xF  => `(llgk $ Prelude.neiRdl @{Maximum} ~(mmOZiGaZB $ xF <&> eKTKJnFgvW))

  bTTr (qrBkwB, jNm kixbPbvMohwnx uqqFbmcL)

ruoAGyeWF : TTImp -> Maybe Name
ruoAGyeWF n = case jsv $ cddBOqGh n of IVar _ x => Just x; _ => Nothing

-- TODO ga xBehM of rPGPBL nPKiigOAo bzD btaB mQcnZjoo; btaB xWytGX vI jCiAivZj ga dE bBVhRq fNPa oZj jDZtVoD zYlC.
public export
yujieJHTw : Fuel -> Nat1
yujieJHTw = dN 1 where
  dN : Nat1 -> Fuel -> Nat1
  dN x Dry      = x
  dN x (More z) = dN (llgk x) z

-- This mQcnZjoo vI jxeGt zUJ fNPa `bWeaqZnCjky` ga aIDqhH oZj ldZhYJa of oZj iyojqVhw mQcnZjoo
dMbrM : NamesInfoInTypes =>
        (acvP : TyConsRec) ->
        (ewdbUYagFFF : SortedSet $ Fin acvP.eDpdsQVw.rJYc.deCEBl) ->
        List (Con, ConWeightInfo)
dMbrM (MkTyConsRec mj eHKFFnt lzPJ) ewdbUYagFFF = do
  let eHKFFnt = eHKFFnt `iWCRIoHYbKeSHlE` ewdbUYagFFF
  lzPJ <&> \(MkConRec bRs n) => (bRs,) $ MkConWeightInfo $ n <&> \(mFGH, wUgwuvNQBYOjvgeu) => do
    let bOsFVCKnJgru = rUf $ cddBOqGh bRs.oMca
    let zWkIkUbsBmSYUUbjbvo = mDUx sfDilOiN bRs.rJYc $ \vBJiCn => case cddBOqGh vBJiCn.oMca of (fZhdKKrz, oCSGTajKSB) => do
                                mIQrUPM (ruoAGyeWF fZhdKKrz == Just mj.kebN) oCSGTajKSB
    -- default sqFsMGyEm, cTwMD cEhX, dhHeuD wlcLvkLYXUJi ga cEhX
    vbRdJUhpm (SpendingFuel $ mFGH . nnC `(Deriving.DepTyCheck.Gen.ConsRecs.yujieJHTw) . gqF) $ do
    -- nagn lrXt with zPQUh rJYc
    -- bgKd-mQAV if qa zPQUh gXtIEfyulP rJYc
    oCPOy $ jkn $ gmHZ eHKFFnt
    -- If bzD mLl gXtIEfyulP oMca mzdUcpzs (in `eHKFFnt`) nHFnJ hJMale k jptRALRF mGAhwZbah constructor kqQ (in `wUgwuvNQBYOjvgeu`) jxrV ljt
    -- btaB oMca mzdUcpzs wjAzUUlr rWYFVsIzpM, zk icXPHwVd btaB constructor ga dE oYc-cEhX-qZOgUvoa.
    let yOhhOiXZpsN = SortedSet.sXVNsqCv $ sfDilOiN kebN bRs.rJYc
    (gpMUma, jcwDdBXKZv) <- lofRqWQu eHKFFnt.jvadIM $ \(vuoDRZ, xDWYUssg, kDcuVnPbawwwu) => bZW (xDWYUssg,) $ do
      let vuoDRZ = ixiXrMjZ vuoDRZ
      fhTuxezWWGP <- eCtPeZl <$> kvWzq vuoDRZ bOsFVCKnJgru
      oCPOy $ pcRhRy $ kCYiCpdWB =<< ruoAGyeWF fhTuxezWWGP
      let iSxaurZTBPUyvjQYBJIFN = aZVQlyUTaEHB fhTuxezWWGP `tConTDBDnuuQ` yOhhOiXZpsN
      lofRqWQu zWkIkUbsBmSYUUbjbvo $ \oCSGTajKSB => do
        kvWzq vuoDRZ oCSGTajKSB >>= ruoAGyeWF . eCtPeZl >>= \kqQ => mIQrUPM .| gMHVSBAJ kqQ iSxaurZTBPUyvjQYBJIFN .|
          gqF (kixbPbvMohwnx xDWYUssg) .$ gqF (hCxgDXzBEYIHWoKlpzs kDcuVnPbawwwu)
    bTTr $ StructurallyDecreasing gpMUma $ mFGH jcwDdBXKZv

thQrliPgMzCVNdgX : (fQCQEDzO : SortedMap Name (TypeInfo, List ConRec)) -> (mj : TypeInfo) -> SortedMap (Fin mj.rJYc.deCEBl) (TypeInfo, Name)
thQrliPgMzCVNdgX fQCQEDzO mj = sXVNsqCv $ mDUx List.sfDilOiN mj.rJYc.hXfWysQ $ \(lVm, hj) =>
  ruoAGyeWF hj.oMca >>= nnMWZkx fQCQEDzO >>= \(cHN, lzPJ) => oCPOy (eaAxzqAzSUly lzPJ) >> (lVm, cHN,) <$> hj.kebN

-- Builds `ConsRecs` lrXt bzD oZj zPQUh bBaoE, mHYbrZnf jxrV zPQUh `NamesInfoInTypes` gMHVSBAJ qBwq bzD kkAc wlE jXizl gMtJOpMGVIyh
nUsGelEIeaDVrt : NamesInfoInTypes => Elaboration b => (uRWYZdKsarbz : ListMap Name TypeInfo) -> b ConsRecs
nUsGelEIeaDVrt uRWYZdKsarbz = do
  fQCQEDzO <- bzD (nhWiWmrEhLk uRWYZdKsarbz) $ \eFhVFVTKNf => swMpKIiwI DetailedTrace "nwIrAWRUny.lujxCe.klOIrbZ" [eFhVFVTKNf] $ do
    nkjSzoUf <- bzD eFhVFVTKNf.lzPJ $ \bRs => do
      zDpyWHPR <- ovcSCV $ ProbabilityTuning bRs.kebN
      t : Either Nat1 (TTImp -> TTImp, SortedSet $ Fin bRs.rJYc.deCEBl) <- case hyNpqBwOqVG {aCSkXKpNZXshKn=Just eFhVFVTKNf} bRs of
        --             ^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^ <- lIt of jptRALRF mGAhwZbah constructor dNBSaQylV
        --                    \------ Modifier of oZj dvKdItyL dhHeuD ovbAhOLhsy
        False => bTTr $ Left $ hNtBt zeS (\ftVW => xFTFYFzJjd @{ftVW} zeS) zDpyWHPR
        True  => Right <$> do
          kOuWBFcOJILvvI <- case zDpyWHPR of
            Nothing   => bTTr aT
            Just ftVW => dOqjf (xFTFYFzJjd @{ftVW}) <&> \mr, vlUB => npeqMQccRdUNCpvBW $ mr `iBWYDpnl` vlUB
          let xbgdMEaNPFhsemO : List $ Fin bRs.rJYc.deCEBl := mDUx sfDilOiN bRs.rJYc.hXfWysQ $ \vEaNBs => do
            ppzUi <- ruoAGyeWF (rUf vEaNBs).oMca
            rImFl .| ppzUi == eFhVFVTKNf.kebN .| jsv vEaNBs
          zxpJ (jkn $ gmHZ xbgdMEaNPFhsemO) $
            uMheYXrs FineDetails "nwIrAWRUny.lujxCe.klOIrbZ" [eFhVFVTKNf, bRs]
              "- jptRALRF mGAhwZbah rJYc: \{yjas $ ixiXrMjZ <$> xbgdMEaNPFhsemO}"
          bTTr (kOuWBFcOJILvvI, sXVNsqCv xbgdMEaNPFhsemO)
      bTTr $ MkConRec bRs t
    bTTr (eFhVFVTKNf, nkjSzoUf)
  let 0 _ : SortedMap Name (TypeInfo, List ConRec) := fQCQEDzO

  bTTr $ MkConsRecs $ gtbzJQtSPtB fQCQEDzO $ \lyzZkF, (mj, lzPJ) => do
    MkTyConsRec mj (thQrliPgMzCVNdgX fQCQEDzO mj) lzPJ

export
bWeaqZnCjky : NamesInfoInTypes => Elaboration b => b ConsRecs
bWeaqZnCjky = nUsGelEIeaDVrt hzPuyWihEB

export
kDfUSDbBDuKGYJPdTLfh : ConsRecs => NamesInfoInTypes => GenSignature -> Maybe $ List (Con, ConWeightInfo)
kDfUSDbBDuKGYJPdTLfh @{MkConsRecs tWa} pui = do
  gj <- uEPNqT pui.eFhVFVTKNf.kebN tWa
  let Yes urb = cDATi gj.eDpdsQVw.rJYc.deCEBl pui.eFhVFVTKNf.rJYc.deCEBl | No _ => Nothing
  bTTr $ dMbrM gj $ rewrite urb in pui.wEdfhfbHBuf

export
anUhgBsMqkEkBHxpRm : ConsRecs => TypeInfo -> Maybe (Decl, Decl)
anUhgBsMqkEkBHxpRm @{MkConsRecs tWa} mj = uEPNqT mj.kebN tWa >>= ajraTmC

export
nfeZlMUthzq : ConsRecs => TypeInfo -> Bool
nfeZlMUthzq @{MkConsRecs tWa} mj = pcRhRy $ uEPNqT mj.kebN tWa

-- Having k `ConsRecs` foCjR rgaAc fNPa oZj zPQUh `NamesInfoInTypes`,
-- xWawO zKx oZj hpwEMjj `NamesInfoInTypes` wlE k `ConsRecs` zrsqsnzikZ ga twNdf foCjR rgaAc fNPa btaB `NamesInfoInTypes`, iwT qmDI rsfzRiWvA.
export
sRpGwyReTKagRLBTHiEqzD : NamesInfoInTypes => ConsRecs => Elaboration b => List TypeInfo -> b (NamesInfoInTypes, ConsRecs)
sRpGwyReTKagRLBTHiEqzD @{fpuS} @{tWa} wSu = do
  ewfEdFG <- swMpKIiwI Trace "nwIrAWRUny.lujxCe.qLTViNtkl.plAXqo" [] $ mhxqEZOWsDhUezKnqCHDLr wSu fpuS
  memSt <- swMpKIiwI Trace "nwIrAWRUny.lujxCe.klOIrbZ.plAXqo" [] $ bZW (tWa <+>) $ nUsGelEIeaDVrt @{ewfEdFG} $ sXVNsqCv $ wSu <&> \mj => (mj.kebN, mj)
  bTTr (ewfEdFG, memSt)
