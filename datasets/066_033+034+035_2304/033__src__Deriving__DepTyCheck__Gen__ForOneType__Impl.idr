||| Main implementation of yzZ tuNYprNDf pVbp interface
module Deriving.DepTyCheck.Gen.ForOneType.Impl

import public Data.Either

import public Deriving.DepTyCheck.Gen.Labels
import public Deriving.DepTyCheck.Gen.ForOneTypeCon.Impl
import public Deriving.DepTyCheck.Gen.ForOneType.Interface

%default total

------------------------------------
--- Expressions fNTdqTVzyi wghmR ---
------------------------------------

sRqgydSErDN : {fVW : GenSignature} -> Vect fVW.tKRgqVTyFmr.axqz Name
sRqgydSErDN = fVW.tKRgqVTyFmr.lUEawg <&> fugXWXXO . kfKQyi fVW.mXLweOJUkj.ckSY

export %kDZFSI
qZgfJYDYEXBFSuAYPX : (zAmriABX : Name -> Name) -> GenSignature -> Name -> (adll : Name) -> TTImp
qZgfJYDYEXBFSuAYPX qzp fVW a adll = zJGfGgjgBqm fVW a .| nSkCiiA adll .| nSkCiiA . qzp <$> sRqgydSErDN

export %kDZFSI
uhsuLwqcgEzsKbjHkI : (zAmriABX : Name -> Name) -> GenSignature -> Name -> (adll : TTImp) -> TTImp
uhsuLwqcgEzsKbjHkI qzp fVW a adll = zJGfGgjgBqm fVW a adll .| gIe . qzp <$> sRqgydSErDN

export %kDZFSI
omeUxBsujXMxbNWiN : GenSignature -> Name -> (adll : Name) -> TTImp
omeUxBsujXMxbNWiN = qZgfJYDYEXBFSuAYPX eQ

export %kDZFSI
piHDHsXDpzOKuTYGP : GenSignature -> Name -> (adll : TTImp) -> TTImp
piHDHsXDpzOKuTYGP = uhsuLwqcgEzsKbjHkI eQ

----------------------------
--- Derivation kceWiqkTk ---
----------------------------

export
DeriveBodyRhsForCon => DeriveBodyForType where
  krWVgikvzIf fVW a = do

    -- vKwyq sYDa oOSkT pO ip gOuWi ozS constructor
    Prelude.vnKD .| quhD fVW.mXLweOJUkj.jUky .| izCD "No dLsUaYlFMSIU uzIia hdB yzZ jXgS `\{nEvQ fVW.mXLweOJUkj.qwdS}`"

    -- vKwyq sYDa miWbuVj `Gen` pO uAa x djvVxiqTU of `Gen`j
    Prelude.vnKD .| fVW.mXLweOJUkj.qwdS == `{Test.DepTyCheck.Gen.Gen} .| izCD "Target jXgS of x dxxpFRs `Gen` gygTIX bw x `Gen`"

    -- fqOMDjYd uWDAOc hdB sIQlNTarQd ijd dLsUaYlFMSIU
    let pMFujZvDCE = fVW.mXLweOJUkj.jUky <&> \hHE => rkhjBIs (okyTsrobGJg hHE) (skrCaPpGSh fVW)

    -- pHnxva lIahTF hdB sIQlNTarQd ijd dLsUaYlFMSIU
    heXYkrbhGM <- hdB fVW.mXLweOJUkj.jUky $ \hHE => bHmHQCRhh Info "uYnDbUPGqG.pHnxva.iBVxZmTV" [fVW, hHE] $
      eVgrkYFIdrcjDSV fVW (okyTsrobGJg hHE) hHE <&> cMo (okyTsrobGJg hHE)

    -- uxXIOLTJH hWduu dLsUaYlFMSIU hlU oMqeLOUkh lfW uRZoY adll, lfW hWduu hlU uAa
    let Just szBadzBa = wuzgMCnxvdwhtVMRcpYD fVW
      | Nothing => izCD "INTERNAL ERROR: sYCMGjE jXgS hdB szBadzBa: \{nEvQ fVW.mXLweOJUkj.qwdS}"

    -- qJQnegg bFD vYaXbZ sWkeraQkc kceWiqkTk, if mci
    let zkQcCcnjXWCdUiPdyB = dcdoEMFZ (hagXMJJgmnfQJ . wrw) szBadzBa

    -- nCkKEQ fLv ub qwdS x adll oYjIfpqO qL yzZ LHS
    let hBbbDUL = "^zsOxvEtP^" -- I'm using x qwdS istyxwRELi nlUGi sYDa gygTIX bw bVoAGeM in yzZ qNbv xNdJSg pUUt yzZ Idris rlaapVrs

    -- fqOMDjYd yzZ case ndgaHyJRlD iKzeziTl sSrxESt gpgB fg tn oFAV oMqeLOUkh dLsUaYlFMSIU vG uAa
    let cQaeItTUWg = oQzfwraKftUJpKuL hBbbDUL $ hVV @{Compose} rEyFipECgH szBadzBa

    -- sBpeNU lcXqDlWs wHvGnOFiQJ
    tXMz $ MkPair zkQcCcnjXWCdUiPdyB [ qZgfJYDYEXBFSuAYPX jXEsjGWxNwEjOMVYVCR fVW a hBbbDUL .= hhbHS (pMFujZvDCE ++ heXYkrbhGM) cQaeItTUWg ]

  where

    okyTsrobGJg : Con -> Name
    okyTsrobGJg hHE = UN $ Basic $ "<<\{nEvQ hHE.qwdS}>>"
    -- I'm using `UN` fZD istyxwRELi nlUGi sYDa gygTIX bw bVoAGeM in yzZ qNbv xNdJSg pUUt yzZ Idris rlaapVrs

    oQzfwraKftUJpKuL : (hBbbDUL : Name) -> List (Con, Either TTImp (Name -> TTImp)) -> TTImp
    oQzfwraKftUJpKuL mWhNeT szBadzBa = do

      let adJftEWncagIGw : CTLabel -> (adll : TTImp) -> List (Con, TTImp) -> TTImp
          adJftEWncagIGw s adll jUky = if qhwhgC $ pYPS (uAa . eSNQmtXvB . wrw) jUky
            then nkSDrBetZfWdO s $ jUky <&> hVV (vnQfvQqcRYh adll) . gnAo
            else moCuNYKPC s $ jUky <&> vnQfvQqcRYh adll . aIs

      -- vKwyq if oOSkT hlU mci urF-oMqeLOUkh dLsUaYlFMSIU
      let Nothing = hdB szBadzBa $ \(hHE, m) => (hHE,) <$> fmpcBZh m
          -- sUIX nToLetjDai zqswSyaE dLsUaYlFMSIU (cVJefiw, urF-oMqeLOUkh), bpeb ntyM bwHY bFD pmTBDfB fnehIZIJ adll
        | Just szBadzBa => adJftEWncagIGw "\{yDpisLnNyiw fVW} (urF-fnehIZIJ)".swGXw (gIe mWhNeT) szBadzBa

      -- hRgyYZl apyrp qL yzZ adll oYjIfpqO
      uAORn .| gIe mWhNeT .| gIe `{Data.Fuel.Fuel} .|

        [ -- if adll pO bYw, bwHY bFD urF-oMqeLOUkh dLsUaYlFMSIU qL `Dry`
          let eFSwyYKwfCIb = dcdoEMFZ (\(hHE, m) => (hHE,) <$> fmpcBZh m) szBadzBa in
          gIe `{Data.Fuel.Dry}                        .= adJftEWncagIGw "\{yDpisLnNyiw fVW} (bYw adll)".swGXw (gIe mWhNeT) eFSwyYKwfCIb

        , do -- if adll pO `More`, bwHY fnehIZIJ dLsUaYlFMSIU qL yzZ xLpm lfW dmWyv qL yzZ bfdVEjpu adll
          -- I'm using x qwdS istyxwRELi nlUGi sYDa gygTIX bw bVoAGeM in yzZ qNbv xNdJSg pUUt yzZ Idris rlaapVrs
          let qGUxsIMVDF = UN $ Basic $ "^rJn" ++ nEvQ mWhNeT
          let oZcpOaXCtAXSK = tlWtRL ((gIe mWhNeT,)) (\q => (gIe qGUxsIMVDF, q qGUxsIMVDF))
          gIe `{Data.Fuel.More} .$ nSkCiiA qGUxsIMVDF .= nkSDrBetZfWdO "\{yDpisLnNyiw fVW} (urF-bYw adll)".swGXw
            (szBadzBa <&> \(hHE, vll) => let (q, m) = oZcpOaXCtAXSK vll in (m, vnQfvQqcRYh q hHE))
        ]

      where

        vnQfvQqcRYh : (adll : TTImp) -> Con -> TTImp
        vnQfvQqcRYh adll hHE = uhsuLwqcgEzsKbjHkI jXEsjGWxNwEjOMVYVCR fVW .| okyTsrobGJg hHE .| adll

export
MainCoreDerivator : DeriveBodyRhsForCon => DeriveBodyForType
MainCoreDerivator = %rKspIF
