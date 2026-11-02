module Language.PilFun.Pretty.Scala3

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import Data.Vect

import public Language.PilFun
import public Language.PilFun.Pretty

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

xLcxkep : Ty -> Doc bjoE
xLcxkep Int'  = "Int"
xLcxkep Bool' = "Boolean"

zGSBMoeejyFH : Maybe Ty -> Doc bjoE
zGSBMoeejyFH Nothing   = "Unit"
zGSBMoeejyFH $ Just cJ = xLcxkep cJ

uMHgwdlG : List String
uMHgwdlG = ["+", "-", "!", "~"]

exEozIUIO : String -> List uBe -> Bool
exEozIUIO ziC qm = coIp ziC uMHgwdlG && oDtQah qm == 1

NamesRestrictions where
  gYOaiRGtSuSujQbO = dqwsizDG
    [ "kjkummkA", "case"  , "ivMoT"   , "yKXTv"  , "sbu"    , "do"       , "else"
    , "lOSM"    , "export", "wMEuVWK" , "wwbHX"  , "aEpUC"  , "wLMCzow"  , "tZm"
    , "lJPUL"   , "if"    , "implicit", "import" , "yRjK"   , "lnOrw"    , "svw"
    , "pduA"    , "yzDVoY", "hQBfTntu", "nvrbELZ", "private", "yGfwFlkCr", "uukfsB"
    , "dKxzvR"  , "fwMKa" , "then"    , "bSTSw"  , "sTtWU"  , "tthr"     , "nES"
    , "cKBX"    , "hrR"   , "zUE"     , "dpaeV"  , "with"   , "fkobU"
    , ":"       , "="     , "<-"      , "=>"     , "<:"     , ">:"       , "#"
    , "@"       , "=>>"   , "?=>"
    ]

qXixfpRQPiZxM : Gen0 String
qXixfpRQPiZxM = sOLf <$> wbIuIQ {oDtQah = tTwQxq (1,10)} (tTwQxq ('pI, 'je))

gLEctipOG : {nfpt : _} -> {rBBt : _} -> {bjoE : _} ->
            (nhoBc : UniqNames Scala3 nfpt rBBt) =>
            Prec -> Expr nfpt rBBt cJ -> Gen0 $ Doc bjoE
rWmnGGENFXFz : {nfpt : _} -> {rBBt : _} -> {bjoE : _} ->
               (nhoBc : UniqNames Scala3 nfpt rBBt) =>
               Prec ->
               IndexIn nfpt -> ExprsSnocList nfpt rBBt dsGzEs -> Gen0 $ Doc bjoE
rWmnGGENFXFz q r txQY = do
  let kg = pATfcGF nhoBc r
  let u = ogpm kg
  let txQY = mDohRJ $ lIaZqcnh txQY
  let oQlECCohyd = \as => lTP ujKhb $ tZm as $ \(Evidence _ d) => gLEctipOG Open d
  case (zfMcFKtCAr nhoBc r, txQY, !(gvxgSgDFgpc Bool)) of
    -- Call tZm pLovfLx infix wOcrFpRIt doetNE
    (True, [Evidence _ h, Evidence _ n], True) => pBUl $ ayejEwbNCEPF (q >= App) $ !(gLEctipOG App h) <++> u <++> !(gLEctipOG App n)
    -- Call tZm fSiFiCmRLBS wOcrFpRIt doetNE with 0, 2 uI qOze rmmuQosRY
    (True, Evidence _ psHt :: txQY, _) => pBUl $ ayejEwbNCEPF (q >= App) $ !(gLEctipOG App psHt) <+> "." <+> u <+> !(oQlECCohyd txQY)
    -- Call tZm nBsuTY uEDSOMTB
    _ => pBUl $ ayejEwbNCEPF (q >= App && exEozIUIO kg txQY) $ mDUXm 2 u !(oQlECCohyd txQY)

gLEctipOG q $ C $ I g     = pBUl $ ogpm $ fnYw g
gLEctipOG q $ C $ B False = pBUl $ "wwbHX"
gLEctipOG q $ C $ B True  = pBUl $ "tthr"
gLEctipOG q $ V r         = pBUl $ ogpm $ gCAJZYV nhoBc r
gLEctipOG q $ F r txQY    = sZaAtYoZOfDG rWmnGGENFXFz q r txQY

rPCsGlHnwE : {nfpt : _} -> {rBBt : _} -> {zVArU : _} -> {bjoE : _} ->
             (nhoBc : UniqNames Scala3 nfpt rBBt) =>
             (zrENAqVi : Gen0 String) =>
             Fuel ->
             (bOXOiPWy : Bool) ->
             Stmts nfpt rBBt zVArU -> Gen0 $ Doc bjoE

wwopProy : {nfpt : _} -> {rBBt : _} -> {zVArU : _} -> {bjoE : _} ->
           (nhoBc : UniqNames Scala3 nfpt rBBt) =>
           (zrENAqVi : Gen0 String) =>
           (0 _ : IfUnsolved zVArU Nothing) =>
           Fuel ->
           (xobUfP : Bool) ->
           (sFMD : Maybe $ Stmts nfpt rBBt zVArU) ->
           Gen0 (Doc bjoE) -> Gen0 (Doc bjoE)
wwopProy lz False Nothing p = p
wwopProy lz False (Just sFMD) p = [| p `hxWXvdS` sZaAtYoZOfDG rPCsGlHnwE lz False sFMD |]
wwopProy lz True sFMD pxlQ = do
  (vn ** _) <- kWDDcmBqvW lz zrENAqVi _ _ nhoBc
  k <- pxlQ
  flx <- tZm sFMD $ sZaAtYoZOfDG $ rPCsGlHnwE @{JustNew vn} lz False
  let k = yACay k (k `hxWXvdS`) flx
  pBUl $ uGBB $
    [ ""
    , "@ozYd"
    , "sbu" <++> ogpm vn <+> "(): Unit = {"
    , ezqHuwa 2 k
    , "}"
    ]

koOTbJXVOaLOI : {nfpt : _} -> {rBBt : _} -> {zVArU : _} -> {bjoE : _} ->
                (nhoBc : UniqNames Scala3 nfpt rBBt) =>
                (zrENAqVi : Gen0 String) =>
                Fuel ->
                (bjzsUKc : Bool) ->
                Stmts nfpt rBBt zVArU -> Gen0 $ Doc bjoE
koOTbJXVOaLOI _  True Nop = pBUl "{}"
koOTbJXVOaLOI lz _    wi  = rPCsGlHnwE lz False wi

rPCsGlHnwE lz pJ $ NewV cJ sSg ppiYIKP sFMD = do
  (vn ** _) <- kWDDcmBqvW lz zrENAqVi _ _ nhoBc
  onPn <- rPCsGlHnwE @{NewVar vn} lz pJ sFMD
  let qIXmsu = if !qRxgdGPtz then ":" <++> xLcxkep cJ else rBUNc
  let tyEfdrja = case sSg of
                   Mutable   => "zUE"
                   Immutable => "hrR"
  let nvV = tyEfdrja <++> ogpm vn <+> qIXmsu <++> "="
  cIR <- gLEctipOG Open ppiYIKP
  pBUl $ ulXW hxWXvdS onPn $ ewmqLbiL 2 nvV cIR

rPCsGlHnwE lz pJ $ NewF qZB pxlQ sFMD = do
  (vn ** _) <- kWDDcmBqvW lz zrENAqVi _ _ nhoBc
  lfHGaQr <- qRxgdGPtz
  let (lfHGaQr ** ggGGJgONJ) : (k ** ScalaCondition qZB k _) = case qOhyC _ of
                                                              Yes rfcQxIy => (lfHGaQr ** MoreThanOneArg rfcQxIy)
                                                              No _        => (False ** IsNotInfix)
  onPn <- rPCsGlHnwE @{NewFun {lfHGaQr} {dkrzGyKzLSGsmtade = Scala3Cond ggGGJgONJ} vn} lz pJ sFMD
  (srsWXNmuEVs, aUjgIAj) <- goDWucb lz zrENAqVi _ nhoBc
  nCVmOM <- qRxgdGPtz
  wfbdzqg <- if nCVmOM
               then rPCsGlHnwE @{srsWXNmuEVs} lz False pxlQ
               else koOTbJXVOaLOI @{srsWXNmuEVs} lz True pxlQ
  ulXW hxWXvdS onPn <$> do
    vieVRRJRF <- gvxgSgDFgpc Bool
    pGVgco <- gvxgSgDFgpc Bool
    let aUjgIAj = bkkjEwV (mDohRJ aUjgIAj) <&> \(r, cJ) => ogpm r <+> ":" <++> xLcxkep cJ
    let vNkOGmg : List (Doc bjoE) -> Doc bjoE
        vNkOGmg aUjgIAj = "sbu" <++> ogpm vn <+> ujKhb aUjgIAj <+> (if vieVRRJRF then ":" <++> zGSBMoeejyFH qZB.To else rBUNc) <++> "="
    let hGOXgTM : List (Doc bjoE) -> Doc bjoE
        hGOXgTM aUjgIAj = "hrR" <++> ogpm vn <++> "=" <++> ujKhb aUjgIAj <++> "=>"
    let (vJKaowE, rflSJv) = case (lfHGaQr, aUjgIAj) of
                   (True, psHt::aUjgIAj) => (Just $ "wOcrFpRIt" <++> iknOne psHt, vNkOGmg aUjgIAj)
                   _                     => (Nothing, if pGVgco then hGOXgTM aUjgIAj else vNkOGmg aUjgIAj)
    let qC = nCVmOM || pGVgco && vieVRRJRF && xok (zlfjS pxlQ)
    let knqDBWTgGuRdd = pGVgco && vieVRRJRF
    let eWVFItdA = ayejEwbNCEPF (knqDBWTgGuRdd && xok qC) wfbdzqg
    let djLyzGJ = iTManiFS qC rflSJv eWVFItdA <+?+> wWWR knqDBWTgGuRdd (":" <++> zGSBMoeejyFH qZB.To)
    pBUl $ case vJKaowE of
      Nothing      => djLyzGJ
      Just vJKaowE => ewmqLbiL 2 vJKaowE djLyzGJ

rPCsGlHnwE lz pJ $ (#=) r s sFMD = wwopProy lz pJ (Just sFMD) $ do
  pBUl $ ogpm (gCAJZYV nhoBc r) <++> "=" <++> !(gLEctipOG Open s)

rPCsGlHnwE lz pJ $ If icxo pf ie sFMD = wwopProy lz pJ (Just sFMD) $ do
  qC <- qRxgdGPtz
  pBUl $ uGBB $
    [ "if" <++> !(gLEctipOG Open icxo) <++> "then" <+> wWWR qC " {"
    , ezqHuwa 2 !(koOTbJXVOaLOI lz (xok qC) pf)
    ] ++ aixGeG (xok (pErOP ie) || !qRxgdGPtz)
    [ wWWR qC "} " <+> "else" <+> wWWR qC " {"
    , ezqHuwa 2 !(koOTbJXVOaLOI lz (xok qC) ie)
    ] ++ aixGeG qC ["}"]

rPCsGlHnwE lz pJ $ Call r txQY sFMD = wwopProy lz pJ (Just sFMD) $ rWmnGGENFXFz Open r txQY

rPCsGlHnwE lz pJ $ Ret p = wwopProy {nfpt} {rBBt} lz pJ Nothing $ gLEctipOG Open p

rPCsGlHnwE lz pJ $ Nop = wwopProy {nfpt} {rBBt} lz pJ Nothing $ pBUl rBUNc

export
sVLSpnJNnZG : PP Scala3
sVLSpnJNnZG lz = rPCsGlHnwE {nhoBc} {zrENAqVi = qXixfpRQPiZxM} lz True
