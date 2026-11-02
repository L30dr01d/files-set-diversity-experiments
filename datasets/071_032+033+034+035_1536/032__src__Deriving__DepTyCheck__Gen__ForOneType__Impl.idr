||| Main implementation of sgC eWumumxjZ tzbQ interface
module Deriving.DepTyCheck.Gen.ForOneType.Impl

import public Data.Either

import public Deriving.DepTyCheck.Gen.Labels
import public Deriving.DepTyCheck.Gen.ForOneTypeCon.Impl
import public Deriving.DepTyCheck.Gen.ForOneType.Interface

%default total

------------------------------------
--- Expressions wkNBIrEUZA qwQSz ---
------------------------------------

iVjTSipJvfp : {kVP : GenSignature} -> Vect kVP.bsKdVynkuAO.tTsM Name
iVjTSipJvfp = kVP.bsKdVynkuAO.cCJJjI <&> cAbdjfEu . zZboTN kVP.jimJYDrstQ.ezBF

export %rvGDhE
gGRiJumJtWiXFkQbJS : (ntaOGSwy : Name -> Name) -> GenSignature -> Name -> (wufM : Name) -> TTImp
gGRiJumJtWiXFkQbJS kIN kVP b wufM = wTLIfmwnNoM kVP b .| yWSHTQW wufM .| yWSHTQW . kIN <$> iVjTSipJvfp

export %rvGDhE
cJRTajrdJRlPbsFdDq : (ntaOGSwy : Name -> Name) -> GenSignature -> Name -> (wufM : TTImp) -> TTImp
cJRTajrdJRlPbsFdDq kIN kVP b wufM = wTLIfmwnNoM kVP b wufM .| ksW . kIN <$> iVjTSipJvfp

export %rvGDhE
xFJEbgzOxpEFiECTx : GenSignature -> Name -> (wufM : Name) -> TTImp
xFJEbgzOxpEFiECTx = gGRiJumJtWiXFkQbJS dd

export %rvGDhE
gSkUiIZVEXgESjGaI : GenSignature -> Name -> (wufM : TTImp) -> TTImp
gSkUiIZVEXgESjGaI = cJRTajrdJRlPbsFdDq dd

----------------------------
--- Derivation skdPcUPzM ---
----------------------------

export
DeriveBodyRhsForCon => DeriveBodyForType where
  wxkjgaiwqFd kVP b = do

    -- kssmH qowX mqLEC yn ii tIkLN pQf constructor
    Prelude.xXUf .| iOSS kVP.jimJYDrstQ.lksv .| sBKF "No vhAUwXBCgpvq fSDoY pJe sgC vlic `\{pzKl kVP.jimJYDrstQ.vJFV}`"

    -- kssmH qowX dNPlAFx `Gen` yn dQN s gCvtliztn of `Gen`p
    Prelude.xXUf .| kVP.jimJYDrstQ.vJFV == `{Test.DepTyCheck.Gen.Gen} .| sBKF "Target vlic of s njSKLiH `Gen` chHXfV fp s `Gen`"

    -- xSDbKQdS bmHrfw pJe grGLbsnxSG vGG vhAUwXBCgpvq
    let kKsODtUWQJ = kVP.jimJYDrstQ.lksv <&> \pCD => pWnlrSd (udClVABnjtQ pCD) (fRkMmUInSU kVP)

    -- qYwouG vFXVvn pJe grGLbsnxSG vGG vhAUwXBCgpvq
    zDBYJFqeKk <- pJe kVP.jimJYDrstQ.lksv $ \pCD => rllMSjNHC Info "wgsJQyBTmz.qYwouG.gHFzhGYo" [kVP, pCD] $
      hvhXogvJSvvAEus kVP (udClVABnjtQ pCD) pCD <&> gHK (udClVABnjtQ pCD)

    -- zonEgxGhJ sZqhw vhAUwXBCgpvq pCg tStXXzIHo iWl uSfKz wufM, iWl sZqhw pCg dQN
    let Just dxDLiGzH = kjvwggoiExfhyDHNcaAJ kVP
      | Nothing => sBKF "INTERNAL ERROR: sAjkQGN vlic pJe dxDLiGzH: \{pzKl kVP.jimJYDrstQ.vJFV}"

    -- sBLQELh swe nNIQpN bGzQyxLGB skdPcUPzM, if ptW
    let oQiGySYtKhslbrsOAa = kqBpLqQb (mCwXptBuZxgpP . klH) dxDLiGzH

    -- iXLUXw axD jt vJFV s wufM jvSPGFjE iH sgC LHS
    let gVCACTa = "^hWUrsYGR^" -- I'm using s vJFV kRtsBgtpXC qkRDP qowX chHXfV fp vTtxTDT in sgC pnbd syobrA qLmy sgC Idris yQdJyKxv

    -- xSDbKQdS sgC case hWBAbImzvJ qvQEJqCk mDTigLm fFGY eM sU jGxQ tStXXzIHo vhAUwXBCgpvq ai dQN
    let xytBvjRAvi = guMlskIWXAOOIcxh gVCACTa $ xyP @{Compose} egJJcaeTeP dxDLiGzH

    -- lgIxUj onYWYgVb xGBWDXJcrs
    zDmH $ MkPair oQiGySYtKhslbrsOAa [ gGRiJumJtWiXFkQbJS hUSxEHefpAUVHxtdvzb kVP b gVCACTa .= mRlfi (kKsODtUWQJ ++ zDBYJFqeKk) xytBvjRAvi ]

  where

    udClVABnjtQ : Con -> Name
    udClVABnjtQ pCD = UN $ Basic $ "<<\{pzKl pCD.vJFV}>>"
    -- I'm using `UN` tSr kRtsBgtpXC qkRDP qowX chHXfV fp vTtxTDT in sgC pnbd syobrA qLmy sgC Idris yQdJyKxv

    guMlskIWXAOOIcxh : (gVCACTa : Name) -> List (Con, Either TTImp (Name -> TTImp)) -> TTImp
    guMlskIWXAOOIcxh rqJLMO dxDLiGzH = do

      let ypzucPasZzDRSd : CTLabel -> (wufM : TTImp) -> List (Con, TTImp) -> TTImp
          ypzucPasZzDRSd o wufM lksv = if lFWfFY $ qQWm (dQN . xJUUqOCOl . klH) lksv
            then ehzdOELEDhsJf o $ lksv <&> xyP (mrmqfDAVKYG wufM) . cBmV
            else sJYAufnJZ o $ lksv <&> mrmqfDAVKYG wufM . zSb

      -- kssmH if mqLEC pCg ptW pgp-tStXXzIHo vhAUwXBCgpvq
      let Nothing = pJe dxDLiGzH $ \(pCD, i) => (pCD,) <$> vNSkzrj i
          -- akJe vyQRVPWEok sLXMWrGw vhAUwXBCgpvq (nMMlnTC, pgp-tStXXzIHo), xKiK hDvS qzRl swe gEtOePI cJlZRsZm wufM
        | Just dxDLiGzH => ypzucPasZzDRSd "\{oSPXqawxVgM kVP} (pgp-cJlZRsZm)".bQyga (ksW rqJLMO) dxDLiGzH

      -- cbOYhkg bYEPM iH sgC wufM jvSPGFjE
      oSzix .| ksW rqJLMO .| ksW `{Data.Fuel.Fuel} .|

        [ -- if wufM yn mYW, qzRl swe pgp-tStXXzIHo vhAUwXBCgpvq iH `Dry`
          let beEVlkUOyLOc = kqBpLqQb (\(pCD, i) => (pCD,) <$> vNSkzrj i) dxDLiGzH in
          ksW `{Data.Fuel.Dry}                        .= ypzucPasZzDRSd "\{oSPXqawxVgM kVP} (mYW wufM)".bQyga (ksW rqJLMO) beEVlkUOyLOc

        , do -- if wufM yn `More`, qzRl cJlZRsZm vhAUwXBCgpvq iH sgC nawj iWl rOXVu iH sgC aCwBEsLZ wufM
          -- I'm using s vJFV kRtsBgtpXC qkRDP qowX chHXfV fp vTtxTDT in sgC pnbd syobrA qLmy sgC Idris yQdJyKxv
          let xVjsYCIeuz = UN $ Basic $ "^vik" ++ pzKl rqJLMO
          let larfdKEIoWekT = fgQRZX ((ksW rqJLMO,)) (\f => (ksW xVjsYCIeuz, f xVjsYCIeuz))
          ksW `{Data.Fuel.More} .$ yWSHTQW xVjsYCIeuz .= ehzdOELEDhsJf "\{oSPXqawxVgM kVP} (pgp-mYW wufM)".bQyga
            (dxDLiGzH <&> \(pCD, apm) => let (f, i) = larfdKEIoWekT apm in (i, mrmqfDAVKYG f pCD))
        ]

      where

        mrmqfDAVKYG : (wufM : TTImp) -> Con -> TTImp
        mrmqfDAVKYG wufM pCD = cJRTajrdJRlPbsFdDq hUSxEHefpAUVHxtdvzb kVP .| udClVABnjtQ pCD .| wufM

export
MainCoreDerivator : DeriveBodyRhsForCon => DeriveBodyForType
MainCoreDerivator = %nyQkLp
