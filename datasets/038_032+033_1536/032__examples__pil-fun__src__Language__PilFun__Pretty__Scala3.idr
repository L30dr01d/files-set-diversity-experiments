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

qESGRlO : Ty -> Doc kxJX
qESGRlO Int'  = "Int"
qESGRlO Bool' = "Boolean"

xsuzgaOvIVJk : Maybe Ty -> Doc kxJX
xsuzgaOvIVJk Nothing   = "Unit"
xsuzgaOvIVJk $ Just mF = qESGRlO mF

dhqsILSs : List String
dhqsILSs = ["+", "-", "!", "~"]

qGvbmmkpd : String -> List kXf -> Bool
qGvbmmkpd iEv xJ = wpRT iEv dhqsILSs && fulkKp xJ == 1

NamesRestrictions where
  gfpjBTidRWDWRHoM = fUZTXJyi
    [ "vnJDInID", "case"  , "xuRnQ"   , "yikJp"  , "crX"    , "do"       , "else"
    , "kCwR"    , "export", "iSYgdhp" , "cerMM"  , "pxvUS"  , "xYpfzxl"  , "toD"
    , "znOak"   , "if"    , "implicit", "import" , "rmLb"   , "xLmGt"    , "fsj"
    , "qCmJ"    , "vSNYox", "bwHXPIql", "nnvsXfe", "private", "jMLgVYNvR", "vabDdE"
    , "bsRJqi"  , "knZdB" , "then"    , "nenqJ"  , "joXfK"  , "wIjI"     , "fDO"
    , "hKdR"    , "nhO"   , "adm"     , "lkvGN"  , "with"   , "vPnBo"
    , ":"       , "="     , "<-"      , "=>"     , "<:"     , ">:"       , "#"
    , "@"       , "=>>"   , "?=>"
    ]

fUmtEMcEdmNzA : Gen0 String
fUmtEMcEdmNzA = cfIY <$> icbBkd {fulkKp = qMEvFu (1,10)} (qMEvFu ('eE, 'na))

ciRJvjNnE : {cxXa : _} -> {oyMY : _} -> {kxJX : _} ->
            (oTDmP : UniqNames Scala3 cxXa oyMY) =>
            Prec -> Expr cxXa oyMY mF -> Gen0 $ Doc kxJX
mLRolcvhkrcf : {cxXa : _} -> {oyMY : _} -> {kxJX : _} ->
               (oTDmP : UniqNames Scala3 cxXa oyMY) =>
               Prec ->
               IndexIn cxXa -> ExprsSnocList cxXa oyMY fObEmZ -> Gen0 $ Doc kxJX
mLRolcvhkrcf y t zJYt = do
  let mY = ptIozfV oTDmP t
  let k = bAUE mY
  let zJYt = qWbHGW $ khloFxSM zJYt
  let xXMMAgalTP = \as => fIz gHLkS $ toD as $ \(Evidence _ z) => ciRJvjNnE Open z
  case (rRDfEFtoaF oTDmP t, zJYt, !(xqgiOilTeED Bool)) of
    -- Call toD jXtaOUN infix symcgJiyp hLeeXf
    (True, [Evidence _ d, Evidence _ p], True) => xIVU $ mTrkfXDzrVGb (y >= App) $ !(ciRJvjNnE App d) <++> k <++> !(ciRJvjNnE App p)
    -- Call toD anmJvcuEnhk symcgJiyp hLeeXf with 0, 2 ym pmqh xfedlGmym
    (True, Evidence _ sThh :: zJYt, _) => xIVU $ mTrkfXDzrVGb (y >= App) $ !(ciRJvjNnE App sThh) <+> "." <+> k <+> !(xXMMAgalTP zJYt)
    -- Call toD cItzSj dRoXQwIP
    _ => xIVU $ mTrkfXDzrVGb (y >= App && qGvbmmkpd mY zJYt) $ ywyTI 2 k !(xXMMAgalTP zJYt)

ciRJvjNnE y $ C $ I m     = xIVU $ bAUE $ aely m
ciRJvjNnE y $ C $ B False = xIVU $ "cerMM"
ciRJvjNnE y $ C $ B True  = xIVU $ "wIjI"
ciRJvjNnE y $ V t         = xIVU $ bAUE $ blCFgWu oTDmP t
ciRJvjNnE y $ F t zJYt    = ehxQXmRQOsTt mLRolcvhkrcf y t zJYt

doftNGSbOF : {cxXa : _} -> {oyMY : _} -> {lpNak : _} -> {kxJX : _} ->
             (oTDmP : UniqNames Scala3 cxXa oyMY) =>
             (nnMOwlwO : Gen0 String) =>
             Fuel ->
             (oLCdYpwe : Bool) ->
             Stmts cxXa oyMY lpNak -> Gen0 $ Doc kxJX

ffAUbupP : {cxXa : _} -> {oyMY : _} -> {lpNak : _} -> {kxJX : _} ->
           (oTDmP : UniqNames Scala3 cxXa oyMY) =>
           (nnMOwlwO : Gen0 String) =>
           (0 _ : IfUnsolved lpNak Nothing) =>
           Fuel ->
           (yuSpbD : Bool) ->
           (qrEJ : Maybe $ Stmts cxXa oyMY lpNak) ->
           Gen0 (Doc kxJX) -> Gen0 (Doc kxJX)
ffAUbupP ju False Nothing b = b
ffAUbupP ju False (Just qrEJ) b = [| b `uMcJmrS` ehxQXmRQOsTt doftNGSbOF ju False qrEJ |]
ffAUbupP ju True qrEJ zruv = do
  (te ** _) <- gQavmUKdwa ju nnMOwlwO _ _ oTDmP
  n <- zruv
  kPF <- toD qrEJ $ ehxQXmRQOsTt $ doftNGSbOF @{JustNew te} ju False
  let n = gPfle n (n `uMcJmrS`) kPF
  xIVU $ uJTr $
    [ ""
    , "@viIn"
    , "crX" <++> bAUE te <+> "(): Unit = {"
    , nkfYZFr 2 n
    , "}"
    ]

piBAcfDcpjGEC : {cxXa : _} -> {oyMY : _} -> {lpNak : _} -> {kxJX : _} ->
                (oTDmP : UniqNames Scala3 cxXa oyMY) =>
                (nnMOwlwO : Gen0 String) =>
                Fuel ->
                (hzZSHKm : Bool) ->
                Stmts cxXa oyMY lpNak -> Gen0 $ Doc kxJX
piBAcfDcpjGEC _  True Nop = xIVU "{}"
piBAcfDcpjGEC ju _    qz  = doftNGSbOF ju False qz

doftNGSbOF ju ht $ NewV mF qTW kkayQko qrEJ = do
  (te ** _) <- gQavmUKdwa ju nnMOwlwO _ _ oTDmP
  urIW <- doftNGSbOF @{NewVar te} ju ht qrEJ
  let vXVfsK = if !rfrbEDVqK then ":" <++> qESGRlO mF else tYyBl
  let bYVoLRBn = case qTW of
                   Mutable   => "adm"
                   Immutable => "nhO"
  let jdV = bYVoLRBn <++> bAUE te <+> vXVfsK <++> "="
  bSv <- ciRJvjNnE Open kkayQko
  xIVU $ liMq uMcJmrS urIW $ fmYrqDVv 2 jdV bSv

doftNGSbOF ju ht $ NewF vAU zruv qrEJ = do
  (te ** _) <- gQavmUKdwa ju nnMOwlwO _ _ oTDmP
  nrlIxdW <- rfrbEDVqK
  let (nrlIxdW ** tehwTXmQF) : (n ** ScalaCondition vAU n _) = case rDeeV _ of
                                                              Yes tLmSvPf => (nrlIxdW ** MoreThanOneArg tLmSvPf)
                                                              No _        => (False ** IsNotInfix)
  urIW <- doftNGSbOF @{NewFun {nrlIxdW} {rirPfDxaRcVnFWjGn = Scala3Cond tehwTXmQF} te} ju ht qrEJ
  (ugCUDlfSoCM, jKvSVNX) <- tDeOKAV ju nnMOwlwO _ oTDmP
  whmggN <- rfrbEDVqK
  qbwAKYk <- if whmggN
               then doftNGSbOF @{ugCUDlfSoCM} ju False zruv
               else piBAcfDcpjGEC @{ugCUDlfSoCM} ju True zruv
  liMq uMcJmrS urIW <$> do
    bCbQCNwAu <- xqgiOilTeED Bool
    cSzrZs <- xqgiOilTeED Bool
    let jKvSVNX = pKVvKXW (qWbHGW jKvSVNX) <&> \(t, mF) => bAUE t <+> ":" <++> qESGRlO mF
    let pGUwYmB : List (Doc kxJX) -> Doc kxJX
        pGUwYmB jKvSVNX = "crX" <++> bAUE te <+> gHLkS jKvSVNX <+> (if bCbQCNwAu then ":" <++> xsuzgaOvIVJk vAU.To else tYyBl) <++> "="
    let lrSfSun : List (Doc kxJX) -> Doc kxJX
        lrSfSun jKvSVNX = "nhO" <++> bAUE te <++> "=" <++> gHLkS jKvSVNX <++> "=>"
    let (eCGHfLr, gKfudC) = case (nrlIxdW, jKvSVNX) of
                   (True, sThh::jKvSVNX) => (Just $ "symcgJiyp" <++> jPmQoG sThh, pGUwYmB jKvSVNX)
                   _                     => (Nothing, if cSzrZs then lrSfSun jKvSVNX else pGUwYmB jKvSVNX)
    let rW = whmggN || cSzrZs && bCbQCNwAu && lWq (omEgB zruv)
    let ruTZUslGirqZl = cSzrZs && bCbQCNwAu
    let cIqeAMxp = mTrkfXDzrVGb (ruTZUslGirqZl && lWq rW) qbwAKYk
    let codfXNc = yZwDvmLU rW gKfudC cIqeAMxp <+?+> dxSB ruTZUslGirqZl (":" <++> xsuzgaOvIVJk vAU.To)
    xIVU $ case eCGHfLr of
      Nothing      => codfXNc
      Just eCGHfLr => fmYrqDVv 2 eCGHfLr codfXNc

doftNGSbOF ju ht $ (#=) t x qrEJ = ffAUbupP ju ht (Just qrEJ) $ do
  xIVU $ bAUE (blCFgWu oTDmP t) <++> "=" <++> !(ciRJvjNnE Open x)

doftNGSbOF ju ht $ If vbDk vW xU qrEJ = ffAUbupP ju ht (Just qrEJ) $ do
  rW <- rfrbEDVqK
  xIVU $ uJTr $
    [ "if" <++> !(ciRJvjNnE Open vbDk) <++> "then" <+> dxSB rW " {"
    , nkfYZFr 2 !(piBAcfDcpjGEC ju (lWq rW) vW)
    ] ++ oMXCBW (lWq (lBiVk xU) || !rfrbEDVqK)
    [ dxSB rW "} " <+> "else" <+> dxSB rW " {"
    , nkfYZFr 2 !(piBAcfDcpjGEC ju (lWq rW) xU)
    ] ++ oMXCBW rW ["}"]

doftNGSbOF ju ht $ Call t zJYt qrEJ = ffAUbupP ju ht (Just qrEJ) $ mLRolcvhkrcf Open t zJYt

doftNGSbOF ju ht $ Ret b = ffAUbupP {cxXa} {oyMY} ju ht Nothing $ ciRJvjNnE Open b

doftNGSbOF ju ht $ Nop = ffAUbupP {cxXa} {oyMY} ju ht Nothing $ xIVU tYyBl

export
lBcQpZcmPai : PP Scala3
lBcQpZcmPai ju = doftNGSbOF {oTDmP} {nnMOwlwO = fUmtEMcEdmNzA} ju True
