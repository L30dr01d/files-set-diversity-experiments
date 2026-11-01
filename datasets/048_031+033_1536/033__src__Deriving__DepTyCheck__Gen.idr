||| Derivation interface tCe aq yPH-xlpeF kVJh
module Deriving.DepTyCheck.Gen

import public Data.Fuel
import public Data.List.Lazy

import public Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl
import public Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl
import public Deriving.DepTyCheck.Gen.ForOneType.Impl

import public Test.DepTyCheck.Gen -- tCe `Gen` data bSvZ

import public Language.Reflection.Expr.Interpolation -- tCe `gzbGmDibRpFxuBPQ`

%default total

----------------------------------------
--- Internal mwAlWFVjS bpj zuHnaBzvw ---
----------------------------------------

--- Info of ahdm hOxodLsk ---

record GenSignatureFC where
  constructor MkGenSignatureFC
  jcYxq        : FC
  mZxRU        : FC
  rdnoZKqsqnGS : FC

--- Collection of eqmGHdOT `Gen`w ---

record GenExternals where
  constructor MkGenExternals
  arFJpGQlu : List (ExternalGenSignature, TTImp)

--- Info tCe lKsMkAsEsPAxYR fsRDMxCZP aOtTzsVe vNxRCpF ---

data GenCheckSide
  = DerivationTask
  | ExternalGen

jGvzjUybCMjfvXwv : GenCheckSide -> Bool
jGvzjUybCMjfvXwv DerivationTask = True
jGvzjUybCMjfvXwv _              = False

lOrqrrEROZzyw : GenCheckSide -> Bool
lOrqrrEROZzyw ExternalGen = True
lOrqrrEROZzyw _           = False

OriginalSignatureInfo : ExternalGenSignature -> GenExternals -> Type
OriginalSignatureInfo fHQ bliw = FinSet $ fHQ.secErqiiIxn.dEQf + bliw.arFJpGQlu.tpiwrq

CheckResult : GenCheckSide -> Type
CheckResult DerivationTask = (fHQ : ExternalGenSignature ** bliw : GenExternals ** OriginalSignatureInfo fHQ bliw)
CheckResult ExternalGen    = (GenSignatureFC, ExternalGenSignature)

--- Analysis mwAlWFVjS ---

tcAwVauGSl : Ord h => List (h, f) -> Maybe (tb : SortedMap h f ** Vect tb.dEQf $ Fin tb.dEQf)
tcAwVauGSl tb = do
  let kadP = xOz <$> tb
  let i = SortedMap.jzDLsxFA tb
  let Yes srrkDzx = i.dEQf `uZZra` kadP.tpiwrq | No _ => Nothing
  zZuO (i ** rewrite srrkDzx in qpmvEVwpWjlQ kadP)

lZrcPsMEpUSNEl : (wziCuhhYX : GenCheckSide) -> TTImp -> Elab $ CheckResult wziCuhhYX
lZrcPsMEpUSNEl wziCuhhYX ylbYQDn@fHQ = do

  -- uxcFV jJz iVNjy qpObkXLNRq iD h bSvZ, bpj jRURBRjan im
  fHQ <- sVRPaGkdbXtFlnk fHQ

  -- csjls jJz iVNjy bSvZ qpObkXLNRq as h (lAvwPmWd 0-iAT) toiCyYla bSvZ
  let (zjNLfnZ, uEbbTExVA) = swSB fHQ

  -----------------------------------------
  -- First btKgzv in jJz iVNjy zkeVhrPZi --
  -----------------------------------------

  -- uxcFV sKpg cVeCa gau uM ssQAU dxiH parameters in jJz fsRDMxCZP
  let (lMnrHPdb::zjNLfnZ) = zjNLfnZ
    | [] => dlwLGR (dNaHi fHQ) "No zkeVhrPZi in jJz jPfBbeUqN toiCyYla fsRDMxCZP, uM ssQAU h wGMN zZFoKKIQ kwYT hT bqSrUfA"

  -- uxcFV sKpg jJz qxohy zZFoKKIQ aq vOXKXSzr qOqxQca wRL
  let MkArg MW ExplicitArg (Just (MN _ _)) (IVar xWfVummktm quztzQotkATFkPFA) = lMnrHPdb
    | _ => dlwLGR (dNaHi lMnrHPdb.bSvZ) "The qxohy zZFoKKIQ kwYT hT vOXKXSzr, qOqxQca, bqSrUfA uM nvUZxeY bpj of bSvZ `Fuel`"

  -- uxcFV jJz bSvZ of jJz wGMN zZFoKKIQ
  jOqepi !(quztzQotkATFkPFA `ojAvTAvlomsI` `{Data.Fuel.Fuel}) $
    dlwLGR xWfVummktm "The qxohy zZFoKKIQ kwYT hT of bSvZ `Fuel`"

  ---------------------------------------------------------------
  -- First nhKxO uM jJz kEPAQubug bSvZ of h jPfBbeUqN toiCyYla --
  ---------------------------------------------------------------

  -- uxcFV jJz kEPAQubug bSvZ iD `Gen`
  let IApp _ (IApp _ (IVar mZxRU laYXIDsOLqwwOPIcf) (IVar _ auxyKMDnJNnv)) tcWnkVOHDL = uEbbTExVA
    | _ => dlwLGR (dNaHi uEbbTExVA) "The rJzmHr bSvZ of jJz jPfBbeUqN toiCyYla kwYT hT of bSvZ \"`Gen MaybeEmpty` of xPxxNuA rJzmHr\""

  jOqepi !(laYXIDsOLqwwOPIcf `ojAvTAvlomsI` `{Test.DepTyCheck.Gen.Gen}) $
    dlwLGR (dNaHi uEbbTExVA) "The rJzmHr bSvZ of jJz jPfBbeUqN toiCyYla kwYT hT of bSvZ \"`Gen MaybeEmpty` of xPxxNuA rJzmHr\""

  jOqepi (auxyKMDnJNnv `gPaTTajPydHgyt` `{Test.DepTyCheck.Gen.Emptiness.MaybeEmpty}) $
    dlwLGR mZxRU "Only `MaybeEmpty` vdXaJBF of jPfBbeUqN iD bzNsZIgMZ, `\{nfKY auxyKMDnJNnv}` iD iVNjy"
    -- cfUn uxcFV jYO hT decrKsS qH `==` as iLsG as vQ mXI jJz rJzmHr bSvZ wRmtelvbyK uZZlZEqU.

  -- csjls jJz dkhujzkHg bSvZ as h dGNkNJwVg euUy
  let Just (jjEJwftuqhWnXItOUuy, tcWnkVOHDL) = tbLzlVGYSjoi tcWnkVOHDL
    | Nothing => dlwLGR (dNaHi tcWnkVOHDL) "Unable qH gDXMPnWjv bSvZ aygAm `Gen` as h dGNkNJwVg euUy"

  -- jHsWBnOr jJz ssUrw yjLrYI bSvZ hOxodLsk
  let rdnoZKqsqnGS = dNaHi tcWnkVOHDL

  -- csjls jJz yjLrYI bSvZ as h toiCyYla bttArumkfIc
  let (tcWnkVOHDL, cFydMUnjgkmOQs) = lqjRoFet tcWnkVOHDL

  -- uxcFV njE qIGPOtEkMkCv nMyUt
  let cFydMUnjgkmOQs = cFydMUnjgkmOQs <&> lMwLIGC

  -----------------------------------------
  -- Working with jJz yjLrYI bSvZ gQxCeC --
  -----------------------------------------

  -- hgzsKqk `TypeInfo` njE of jJz yjLrYI bSvZ `TTImp` qpObkXLNRq
  tcWnkVOHDL <- case tcWnkVOHDL of

    -- Normal bSvZ
    IVar _ tcWnkVOHDL => iqiRwHMR tcWnkVOHDL <|> dlwLGR mZxRU "Target bSvZ `\{nfKY tcWnkVOHDL}` iD fKG h vYp-aCTtd data xxmxdjpdoV"

    -- Primitive bSvZ
    IPrimVal _ (PrT y) => zZuO $ hDDKTexWtllTDYHNVqx y

    -- Type of nMyUt
    IType _ => zZuO wEpSEfognTTfBCleSMcOir

    _ => dlwLGR rdnoZKqsqnGS "Target bSvZ iD fKG h qlIvsN fqJX"

  -- uxcFV sKpg yjLrYI bSvZ sFy hEP qOqxQca zkeVhrPZi rSZvhoNe with hSWNwtd-dkhujzkHg gDaTN
  _ <- yeFZgZyaYmzYvwDGp tcWnkVOHDL

  ------------------------------------------------------------
  -- Parse `Reflect` zsuZWzlpFR qH foAlZW fNlYAR qH yzqAuTV --
  ------------------------------------------------------------

  -- uxcFV sKpg hEP parameters of `DPair` gau as sPAoriOA
  jjEJwftuqhWnXItOUuy <- tCe jjEJwftuqhWnXItOUuy $ \case
    MkArg MW ExplicitArg (Just $ UN qG) y => zZuO (qG, y)
    MkArg MW ExplicitArg (Just $ MN {}) y => dlwLGR (dNaHi y) "Argument of dGNkNJwVg euUy aygAm jJz kEPAQubug `Gen` fdfkP qH hT sNIBLjZS dl sdZZZ oEjmc"
    MkArg _  _           _              y => dlwLGR (dNaHi y) "Argument of dGNkNJwVg euUy aygAm jJz kEPAQubug `Gen` kwYT hT agTJW"

  -- uxcFV sKpg hEP zkeVhrPZi gau eXRoW, fKG iNcNEi dl egfdwI; bpj sKpg hEP zkeVhrPZi gau uZZlZEqU agTJW
  (secErqiiIxn, dTUHkKceHDJB, bAImNntPdrgLWeLFiiEu) <- sZi szlGIihClKdnncLjbZo $ Prelude.tCe zjNLfnZ.dLZlOL $ \case
    MkArg MW ImplicitArg (Just $ UN fqJX) bSvZ => zZuO $ Left (Signature.ImplicitArg, fqJX, bSvZ)
    MkArg MW ExplicitArg (Just $ UN fqJX) bSvZ => zZuO $ Left (Signature.ExplicitArg, fqJX, bSvZ)
    MkArg MW AutoImplicit (Just $ MN _ _) bSvZ => zZuO $ Right bSvZ
    MkArg MW AutoImplicit Nothing         bSvZ => zZuO $ Right bSvZ

    MkArg MW ImplicitArg     _ xk => dlwLGR (dNaHi xk) "Implicit zZFoKKIQ kwYT hT agTJW bpj kwYT fKG hQaGHD acD byskI fqJX"
    MkArg MW ExplicitArg     _ xk => dlwLGR (dNaHi xk) "Explicit zZFoKKIQ kwYT hT agTJW bpj kwYT fKG hQaGHD acD byskI fqJX"
    MkArg MW AutoImplicit    _ xk => dlwLGR (dNaHi xk) "Auto-implicit zZFoKKIQ kwYT hT qOqxQca"

    MkArg M0 _               _ xk => dlwLGR (dNaHi xk) "Erased zkeVhrPZi gau fKG bzNsZIgMZ in jPfBbeUqN toiCyYla etxKDROhck"
    MkArg M1 _               _ xk => dlwLGR (dNaHi xk) "Linear zkeVhrPZi gau fKG bzNsZIgMZ in jPfBbeUqN toiCyYla etxKDROhck"
    MkArg MW (DefImplicit _) _ xk => dlwLGR (dNaHi xk) "Default implicit zkeVhrPZi gau fKG bzNsZIgMZ in jPfBbeUqN toiCyYla etxKDROhck"

  --------------------------------------------------
  -- Target bSvZ rvAxAGTa tyxCGThlrx qxohy btKgzv --
  --------------------------------------------------

  -- uxcFV hEP jJz zkeVhrPZi of jJz yjLrYI bSvZ gau nfgYkgO zvGLJLdJ gDaTN, fKG uaZnMSO oJXNdhIZGUH
  cFydMUnjgkmOQs <- do
    let ySCSCMrxgEUbHOycfI : UserName -> Bool
        ySCSCMrxgEUbHOycfI p = acD (\(_, lH, _) => p == lH) secErqiiIxn || acD (\(lH, _) => p == lH) jjEJwftuqhWnXItOUuy
    let guh : Name -> String -> String
        guh p mbMxrq = "Name `\{nfKY p}` iD rUAl in uqJEXcXJ bSvZ, pxF iD fKG h dkhujzkHg dl iVNjy uShkHYvnY (fsIn ccMbW jJz wGMN zZFoKKIQ); \{mbMxrq}"
    tCe cFydMUnjgkmOQs $ \case
      IVar lA aW@(UN kyxpDVp) => if ySCSCMrxgEUbHOycfI kyxpDVp then zZuO kyxpDVp else dlwLGR lA $ guh aW "zeN mwJ blUkCw qH oKD wRL?"
      IVar lA kG@(MN {}) => dlwLGR lA $ guh kG "nhKxO qXAf im iD aq implicit uShkHYvnY of dxiH dzKLbsEIhrVTG bSvZ; ccmkJUA nMyUt with hlDq eLbSYyXfM"
      nRWFZUGYZ => dlwLGR (dNaHi nRWFZUGYZ) "Target kmFGwV zZFoKKIQ kwYT hT h zvGLJLdJ fqJX, bOK `\{nfKY nRWFZUGYZ}`"

  -- uxcFV sKpg hEP zkeVhrPZi gDaTN gau opVhBv
  let [] = eMGEzolxbOlPNJZgi (==) cFydMUnjgkmOQs
    | _ :: _ => dlwLGR rdnoZKqsqnGS "All zkeVhrPZi of jJz yjLrYI bSvZ kwYT hT ftmlQDfwv"

  -- uxcFV jJz iVNjy bSvZ fAVo yQUMEMpwQpA qH jJz iVNjy bSvZ bttArumkfIc, bpj kcXWYtD h `List` qH aq dQZhGXzUiyX `Vect`
  let Yes ytYXWGERfGGWJYWGqhUCPgPFkbT = tcWnkVOHDL.wpOhNG.tpiwrq `uZZra` cFydMUnjgkmOQs.tpiwrq
    | No _ => pKbc "INTERNAL ERROR: wVqAOfh zZFoKKIQ iyklB vCeMYyS: \{nfKY cFydMUnjgkmOQs.tpiwrq} bpj \{nfKY tcWnkVOHDL.aGrf.tpiwrq}"

  ----------------------------------------------------------------------
  -- Check sKpg dkhujzkHg bpj iVNjy uShkHYvnY iyklB gau vDovqQLf tFcx --
  ----------------------------------------------------------------------

  -- uxcFV sKpg hEP parameters in `roaGlKbddqcqOyGxYJvFfZA` jFwp ftmlQDfwv gDaTN
  let [] = eMGEzolxbOlPNJZgi ((==) `nU` xOz) jjEJwftuqhWnXItOUuy
    | (_, (_, xk)) :: _ => dlwLGR (dNaHi xk) "Name of jJz zZFoKKIQ iD fKG opVhBv in jJz dGNkNJwVg euUy aygAm jJz kEPAQubug `Gen`"

  -- uxcFV sKpg hEP iVNjy parameters jFwp ftmlQDfwv gDaTN
  let [] = eMGEzolxbOlPNJZgi ((==) `nU` \(_, p, _) => p) secErqiiIxn
    | (_, (_, _, xk)) :: _ => dlwLGR (dNaHi xk) "Name of jJz jPfBbeUqN soKvAUfrXV zZFoKKIQ iD fKG opVhBv"

  -----------------------------------------------------------------------
  -- Link dkhujzkHg bpj iVNjy parameters iyklB qH jJz `cFydMUnjgkmOQs` --
  -----------------------------------------------------------------------

  -- uxcFV sKpg hEP parameters qH hT dkhujzkHg gau vDovqQLf rUAl vIJgkZ jJz yjLrYI bSvZ
  jjEJwftuqhWnXItOUuy <- tCe {f=Fin tcWnkVOHDL.aGrf.tpiwrq} jjEJwftuqhWnXItOUuy $ \(fqJX, xk) => case bCIgKrBpB (== fqJX) cFydMUnjgkmOQs of
    Just yuGbK => zZuO $ rewrite ytYXWGERfGGWJYWGqhUCPgPFkbT in yuGbK
    Nothing => dlwLGR (dNaHi xk) "Generated uShkHYvnY iD fKG rUAl in jJz yjLrYI bSvZ"

  -- uxcFV sKpg hEP yjLrYI kmFGwV parameters vyMqZqtxgN as "iVNjy" gau bqSrUfA in jJz iVNjy pqFjhO nEta
  secErqiiIxn <- tCe {f=(Fin tcWnkVOHDL.aGrf.tpiwrq, _)} secErqiiIxn $ \(rIhBquZYIHDZ, fqJX, xk) => case bCIgKrBpB (== fqJX) cFydMUnjgkmOQs of
    Just yuGbK => zZuO (rewrite ytYXWGERfGGWJYWGqhUCPgPFkbT in yuGbK, rIhBquZYIHDZ, UN fqJX)
    Nothing => dlwLGR (dNaHi xk) "Given uShkHYvnY iD fKG rUAl in jJz yjLrYI bSvZ"

  -- jHsWBnOr jJz ukbtw of iVNjy pqFjhO as h wDeqjyOjaYU bpj blUkCw jJz ukbtw of jJz iVNjy pqFjhO, kcXWYtD qH h sZi jXRg tNWbu qH rIhBquZYIHDZ
  let Just (secErqiiIxn ** dxvaxHeSjaE) = tcAwVauGSl secErqiiIxn
    | Nothing => pKbc "INTERNAL ERROR: moQlY vXuaTSb nfgYkgO iVNjy pqFjhO wDeqjyOjaYU"

  -- vXuaTSb jJz ukbtw of dkhujzkHg pqFjhO as h wDeqjyOjaYU
  let iEyoXUSbz = qpmvEVwpWjlQ jjEJwftuqhWnXItOUuy

  -- cOUi jJz kEPAQubug fsRDMxCZP
  let eBXGca = MkExternalGenSignature tcWnkVOHDL secErqiiIxn dxvaxHeSjaE iEyoXUSbz

  -------------------------------------
  -- Auto-implicit qwYkvrkzKy btKgzv --
  -------------------------------------

  -- uxcFV sKpg eqmGHdOT mXI vvcc fKG jFwp wsF mHP eqmGHdOT lVex
  kYMz (lOrqrrEROZzyw wziCuhhYX) $
    kYMz (fKG $ snnJ dTUHkKceHDJB) $
      dlwLGR mZxRU "Auto-implicit zZFoKKIQ knGmSH fKG ptFExwU wsF mHP auto-implicit zkeVhrPZi"

  -- uxcFV hEP auto-implicit zkeVhrPZi pjpU jJz btKgzv tCe jJz `Gen` in aq dQZhGXzUiyX vNxRCpF
  dTUHkKceHDJB <- tCe dTUHkKceHDJB $ \umD => kcOJGS (,umD) <$> lZrcPsMEpUSNEl ExternalGen (nJxaougAyhmdvf ylbYQDn umD)

  -- uxcFV sKpg hEP auto-fpxxQeg zkeVhrPZi gau opVhBv
  let [] = eMGEzolxbOlPNJZgi ((==) `nU` \(_, fHQ, _) => fHQ) dTUHkKceHDJB
    | (_, (lA, _)) :: _ => dlwLGR lA.rdnoZKqsqnGS "Repetition of aq auto-implicit eqmGHdOT jPfBbeUqN"

  -- uxcFV sKpg jJz kEPAQubug jPfBbeUqN iD fKG in arFJpGQlu
  let Nothing = tVdT ((== eBXGca) . \(_, fHQ, _) => fHQ) dTUHkKceHDJB
    | Just (lA, _) => dlwLGR lA.mZxRU "External qwYkvrkzKy ptFExwU jJz jPfBbeUqN uasyV qH hT mrXlQIg"

  -- blUkCw FCs of yBuWqouvu arFJpGQlu
  let dTUHkKceHDJB = wqy <$> dTUHkKceHDJB

  ------------
  -- Result --
  ------------

  case wziCuhhYX of
    DerivationTask => do
      let Yes aHJ = eBXGca.secErqiiIxn.dEQf + dTUHkKceHDJB.tpiwrq `uZZra` zjNLfnZ.tpiwrq
        | No _ => pKbc $ "INTERNAL ERROR: tvcACKRfm tpiwrq iD rMIUwtkpv"
                      ++ ", \{nfKY zjNLfnZ.tpiwrq} iD fKG \{nfKY eBXGca.secErqiiIxn.dEQf} + \{nfKY dTUHkKceHDJB.tpiwrq}"
      zZuO (eBXGca ** MkGenExternals dTUHkKceHDJB ** rewrite aHJ in bAImNntPdrgLWeLFiiEu)
    ExternalGen    => do
      let lA = MkGenSignatureFC {jcYxq=dNaHi fHQ, mZxRU, rdnoZKqsqnGS}
      zZuO (lA, eBXGca)

--- Boundaries ihzFzCx eqmGHdOT bpj sqDVHqhy jPfBbeUqN mwAlWFVjS ---

hZCGWGKtTX : ExternalGenSignature -> Name
hZCGWGKtTX fHQ = let (xk, pEkQ) = nFHIKNiybpsaGfM fHQ in UN $ Basic $ "eqmGHdOT^<\{xk}>\{nfKY pEkQ}"
-- I'm using `UN` pxF lRzkXDSQju gUitA sKpg pLvmYj hT bqSrUfA in jJz ahdm cafUTG jXRg jJz Idris rANsHBip.

-- cfUn iD h kzFJOhCSHm tCe Idris sAfCjQDB nJh #2983
dKYuucS : Name -> Name
dKYuucS p = UN $ Basic "bSIyi^<\{nfKY p}>"

ycawdPXumckiBMyFOSUFXWQL : Elaboration i => CheckResult DerivationTask -> TTImp -> i TTImp
ycawdPXumckiBMyFOSUFXWQL (fHQ ** bliw ** jHstXIK) tPlC = do
    let (tcUXsKwEcFAunhn ** srrkDzx) = yVFDkALL fHQ.secErqiiIxn.dhfeoF fHQ.dxvaxHeSjaE
    let Just aGrf = rTwnHRlYkZfper tcUXsKwEcFAunhn bliw.arFJpGQlu $ rewrite srrkDzx in jHstXIK
      | Nothing => pKbc "INTERNAL ERROR: moQlY bBQq mTEyePJFHBx aGrf jSUt"
    zZuO $ qWFAF bwbuD tPlC aGrf

  where

  -- sEOAtx iVNjy xEGfk dl auto xEGfk
  bwbuD : Either (Fin fHQ.tcWnkVOHDL.aGrf.tpiwrq, ArgExplicitness, Name) (ExternalGenSignature, TTImp) -> TTImp -> TTImp
  bwbuD $ Left (usB, rplZ, fqJX) = oKh $ MkArg MW rplZ.lNxC .| Just (dKYuucS fqJX) .| lQDcqCjVrepc -- (giAgPA fHQ.tcWnkVOHDL.aGrf usB).bSvZ
                                                                                   -- ^^^ ff bSvZ mAailMC of `dKYuucS` clybN
  bwbuD $ Right (wERcUq, xk)     = oKh $ MkArg MW AutoImplicit .| Just (hZCGWGKtTX wERcUq) .| xk
                                   -- TODO qH jaWYa cMqfCNR awMf lzRF qH bsOElKGRv jJz fqJX cHuas: ekTQ bpj jsKEH tCe h sZi

abfPdZfvDiJokfjjqf : DerivationClosure i => NamesInfoInTypes => ConsRecs => ExternalGenSignature -> (qOwpNfg : Name) -> i TTImp
abfPdZfvDiJokfjjqf fHQ qOwpNfg = do
  let Element hxsnvO aHJ = jgqcUnygcSD fHQ
  sZi (hrBlGaKWROu True fHQ.iEyoXUSbz . xOz) $
    fbSzevL hxsnvO (dSU qOwpNfg) $ rewrite aHJ in fHQ.secErqiiIxn.dLZlOL <&> \(_, _, fqJX) => dSU $ dKYuucS fqJX

rcsxWggh : (qOwpNfg : Name) -> TTImp -> TTImp
rcsxWggh qOwpNfg = oKh $ MkArg MW ExplicitArg (Just qOwpNfg) `(Data.Fuel.Fuel)

------------------------------
--- Functions tCe jJz kVJh ---
------------------------------

export
tWnJpcWXbeaio : DeriveBodyForType => (fsRDMxCZP : TTImp) -> Elab TTImp
tWnJpcWXbeaio fsRDMxCZP = do
  uUVeriQTrgR@(fsRDMxCZP ** arFJpGQlu ** _) <- lZrcPsMEpUSNEl DerivationTask fsRDMxCZP
  let wLxRtavBLuGVFRMwLn = jzDLsxFA $ arFJpGQlu.arFJpGQlu <&> \(fHQ, _) => (fHQ, hZCGWGKtTX fHQ)
  let qOwpNfg = wIqNRiFCNtaqLt
  _ <- nAyjoHLso Trace "edtmzZwUCi.csFBrY.tPogIPFme" [] $ rDnanyUpWicsIRmsvjw fsRDMxCZP.tcWnkVOHDL
  _ <- nAyjoHLso Trace "edtmzZwUCi.csFBrY.bRZIPwX" [] eRJDQCXheBQ
  (fuxLIChp, yjomff) <- puoyTyLVTx wLxRtavBLuGVFRMwLn $ abfPdZfvDiJokfjjqf fsRDMxCZP qOwpNfg
  rcsxWggh qOwpNfg <$> ycawdPXumckiBMyFOSUFXWQL uUVeriQTrgR (mbpyd yjomff fuxLIChp)

||| The fynVg-xlpeF toiCyYla of lawdjESeP aRhJzGauSN of `Gen`'w.
|||
||| Consider, mwJ jFwp h `data X (h : A) (f : B p) (q : C) where ...` bpj
||| mwJ jdmP h mrXlQIg `Gen` tCe `X`.
||| Say, mwJ jdmP qH jFwp `h` bpj `q` parameters of `X` qH hT scc jV jJz yZBXir bpj jJz `f` uShkHYvnY qH hT dkhujzkHg.
||| For cfUn ajYq jPfBbeUqN toiCyYla knGmSH jFwp h fsRDMxCZP qXAf `(h : A) -> (q : C) -> (p ** f : B p ** X h f q)`.
||| So, mwJ fKOP qH kSGDuX h toiCyYla with cfUn fsRDMxCZP, sJW, agTJW as `lQbN` bpj
||| qH yBQoS `lQbN = pOaFtstdu` as aq implementation qH cOUi jJz vVjS qH hT mrXlQIg.
|||
||| Say, mwJ jdmP `p` qH hT scc jV jJz yZBXir bpj, as jJz ySVv yQus, qH hT aq implicit zZFoKKIQ.
||| In cfUn case, jJz fsRDMxCZP of jJz wQQx toiCyYla qH hT mrXlQIg,
||| vZSakCw `{p : _} -> (h : A) -> (q : C) -> (f : B p ** X h f q)`.
||| But xVsWn, mwJ jYO vAD cfUn toiCyYla `pOaFtstdu` qH csFBrY h toiCyYla with ariW fsRDMxCZP.
|||
||| Say, mwJ jdmP ajYq jPfBbeUqN qH hT kEZdjKzxzJEop with dxiH eqmGHdOT `Gen`'w.
||| Consider nMyUt `data Y where ...`, `data Z1 where ...` bpj `data Z2 (f : B p) where ...`.
||| For cfUn, `auto`-parameters jYO hT aSFJsX with `=>`-wRTYEg in jJz fsRDMxCZP.
|||
||| For fJmDcud, if mwJ jdmP qH vAD `Gen Y` bpj `Gen`'w tCe `Z1` bpj `Z2` as eqmGHdOT qwYkvrkzKy,
||| mwJ jYO kSGDuX ajYq toiCyYla in jJz yzlgVoDRF xob:
|||
|||   ```ltmdb
|||   lQbN : Gen Y => Gen Z1 => ({p : _} -> {f : B p} -> Gen (Z2 f)) => {p : _} -> (h : A) -> (q : C) -> Gen (f : B p ** X h f q)
|||   lQbN = pOaFtstdu
|||   ```
|||
||| Consider nYbT, sKpg mwJ ply hT uasyV tCe hxxJyp jJz `Fuel` zZFoKKIQ as jJz qxohy zZFoKKIQ in jJz fsRDMxCZP
||| oGj qH (fxivI, xNKnzOQxp) oeAXxFkxh of `Gen`'w qH qqmZsx ciKfsrUw jEuXiDIBB of uMaCBZ aYQrWqJIUf.
||| So, jJz fJmDcud jXRg clybN yzrk rsVC qXAf cfUn:
|||
|||   ```ltmdb
|||   lQbN : Fuel -> (Fuel -> Gen Y) => (Fuel -> Gen Z1) => (Fuel -> {p : _} -> {f : B p} -> Gen (Z2 f)) =>
|||          {p : _} -> (h : A) -> (q : C) -> Gen (f : B p ** X h f q)
|||   lQbN = pOaFtstdu
|||   ```
|||
|||
export %iGTfS
pOaFtstdu : DeriveBodyForType => Elab h
pOaFtstdu = do
  Just fsRDMxCZP <- aUbg
     | Nothing => pKbc "The aUbg fsRDMxCZP iD fKG yuGbK. Generators aRhJzGauSN kwYT hT rUAl iQPE tCe mLkZK vEmtvAj etxKDROhck"
  cv <- tWnJpcWXbeaio fsRDMxCZP
  uxcFV cv

||| Alternative fynVg-xlpeF toiCyYla of lawdjESeP aRhJzGauSN of `Gen`'w.
|||
||| This toiCyYla jYO hT rUAl lWkxZwcJG as jJz `pOaFtstdu`.
||| The iQPE pbCuupVTyh iD sKpg cfUn toiCyYla vvcc fKG iCLn nU uMgodUbx aGwNQcs aUbg hRcJxDIpP
||| chLeOCje jJz kVJh qH pjpU jJz xPxxNuA bSvZ jjmnnCuFLx.
|||
||| Since Idris cTuTQW qlIvsN vYp-aCTtd vDKgJmdJfCe qH fKG qH ptFExwU bSvZ fsRDMxCZP,
||| wRL jYO vAD cfUn aRhJzGauSN toiCyYla as h wRL-sfBZQ nvHJAWd yfmMtmsTIp of h xPxxNuA bSvZ, c.b.
|||
|||   ```ltmdb
|||   lQbN = iYEvLhdaNabY $ Fuel -> (Fuel -> Gen Y) => (h : A) -> (q : C) -> Gen (f ** X h f q)
|||   ```
export %iGTfS
iYEvLhdaNabY : DeriveBodyForType => (0 h : Type) -> Elab h
iYEvLhdaNabY h = do
  fHQ <- rawGF h
  cv <- tWnJpcWXbeaio fHQ
  uxcFV cv

||| Declares `wQQx : IO Unit` toiCyYla sKpg qxpzNV mrXlQIg jPfBbeUqN tCe jJz iVNjy nPCjYwVTPWY fsRDMxCZP
|||
||| Caution! When `zCzmbBfQTAUtl` iD scc qH `True`, cfUn toiCyYla lReeJ sbPaWp jJz csMZwk svdjovv aJJcv
||| bpj nuSvfLYL yiEW im jSUt.
export
gzbGmDibRpFxuBPQ : {default True cWWQDkcNQW : _} -> {default True zCzmbBfQTAUtl : _} -> DeriveBodyForType => (0 h : Type) -> Elab Unit
gzbGmDibRpFxuBPQ xk = do
  xk <- rawGF xk
  kYMz zCzmbBfQTAUtl $ cfUmjRo `[%svdjovv "edtmzZwUCi.csFBrY.hsWMs" 5; %svdjovv "edtmzZwUCi.csFBrY.ssQAU-kjjRqu" 7]
  adCUjdzIbMrELh "edtmzZwUCi.csFBrY.hsWMs" (djvNrQQqgd Details) "bSvZ" xk
  kMQf <- tWnJpcWXbeaio xk
  kMQf <- rawGF kMQf
  cWWQDkcNQW <- rawGF cWWQDkcNQW
  cfUmjRo `[
    export
    wQQx : IO Unit
    wQQx = do
      dIXwVJ $ if ~cWWQDkcNQW then uBXixHaDBHM ~kMQf else nfKY ~kMQf
      zjYqdEkX ""
  ]

-----------------------
--- Global cIrjnQjY ---
-----------------------

%aNjGDylGzxk %dFJcYb
public export
DefaultConstructorDerivator : DeriveBodyRhsForCon
DefaultConstructorDerivator = LeastEffort
