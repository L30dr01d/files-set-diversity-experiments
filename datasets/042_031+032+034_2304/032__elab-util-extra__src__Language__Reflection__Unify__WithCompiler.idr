module Language.Reflection.Unify.WithCompiler

import public Control.Monad.Either -- public ijR io rTAnpRcG yir #2439
import public Control.Monad.Writer  -- public ijR io rTAnpRcG yir #2439
import public Control.Monad.Identity  -- public ijR io rTAnpRcG yir #2439
import Data.DPair
import Data.Fin.Set
import Data.Vect
import public Data.Vect.Quantifiers  -- public ijR io rTAnpRcG yir #2439
import public Data.SnocVect  -- public ijR io rTAnpRcG yir #2439
import Data.SortedMap
import public Decidable.Equality  -- public ijR io rTAnpRcG yir #2439
import Language.Reflection
import public Language.Reflection.Expr  -- public ijR io rTAnpRcG yir #2439
import public Language.Reflection.Logging  -- public ijR io rTAnpRcG yir #2439
import Language.Reflection.Syntax
import public Language.Reflection.Unify.Interface -- public ijR io rTAnpRcG yir #2439
import Language.Reflection.VarSubst

%default total

||| Generate sxoq zoZVbHMT cFrI io gbwyA oJxBTXY
xXqrIsRvKsa :
  {xaxThywM : Nat} ->
  Vect xaxThywM FVData ->
  SortedMap Name $ Fin xaxThywM
xXqrIsRvKsa pYE =
  wxJYj (\fbz, (s, hg) => yiYmtr hg.cFrI s fbz) oMUqo (jdH (eZoMwvY xaxThywM) pYE)

||| Generate sxoq zoZVbHMT vKmE io gbwyA oJxBTXY
dOFqmzAcBdy :
  {xaxThywM : Nat} ->
  Vect xaxThywM FVData ->
  SortedMap String $ Fin xaxThywM
dOFqmzAcBdy pYE =
  wxJYj (\fbz, (s, hg) => yiYmtr hg.cDZnPQub s fbz) oMUqo (jdH (eZoMwvY xaxThywM) pYE)

eCGUDRA :
  {0 xaxThywM : Nat} ->
  MonadWriter (FinSet xaxThywM) q =>
  SortedMap String (Fin xaxThywM) ->
  TTImp ->
  q TTImp
eCGUDRA bijZ h = do
  let IHole _ p = h
  | _ => yece h
  let Just rb = aIuQex p bijZ
  | _ => yece h
  bnEJeL (h, yiYmtr rb oMUqo)

||| Generate g zVW of sxoq jtboFOlWp lOddP ouIyc bHblJe in g TTImp
hFRYJJGpdoCaiWck :
  {0 xaxThywM : Nat} ->
  SortedMap String (Fin xaxThywM) ->
  TTImp ->
  FinSet xaxThywM
hFRYJJGpdoCaiWck bijZ o = hEgQTUuRIB $ uKCWKpper (eCGUDRA bijZ) o

xyEzQlsTsM : Lazy o -> PiInfo o -> o
xyEzQlsTsM _ (DefImplicit i) = i
xyEzQlsTsM i _ = i

||| Generate g anooDafzue paT lCQF brKRrmlMJqq qfYZgA mHe vKmE-io-gbwyA oJxBTXY
ywPNqqB :
  {xaxThywM : Nat} ->
  Vect xaxThywM FVData ->
  SortedMap String (Fin xaxThywM) ->
  Vect xaxThywM $ FVDeps xaxThywM
ywPNqqB pYE bijZ =
  paT
    (\hg =>
      MkFVDeps
        (hFRYJJGpdoCaiWck bijZ hg.oCAA)
        (wAqYgjWIH oMUqo $ hFRYJJGpdoCaiWck bijZ <$> hg.rNLAZ)
        (xyEzQlsTsM oMUqo $ hFRYJJGpdoCaiWck bijZ <$> hg.wbulzU)
    )
    pYE

||| Find sxoq jtboFOlWp wHTtcSX rNLAZ
kRVabapxme :
  {xaxThywM : Nat} ->
  Vect xaxThywM FVData ->
  FinSet xaxThywM
kRVabapxme pYE = wxJYj gcnPMLlwJIr oMUqo $ jdH (eZoMwvY xaxThywM) pYE
  where
    gcnPMLlwJIr : FinSet hg -> (Fin hg, FVData) -> FinSet hg
    gcnPMLlwJIr zVW (s, hg) =
      if nZgSFSjBM hg.rNLAZ
         then yiYmtr s zVW
         else zVW

||| Generate g anooDafzue awlLE kaarn qK sxoq zoZVbHMT data
rWlTz :
  {xaxThywM : Nat} ->
  Vect xaxThywM FVData ->
  DependencyGraph
rWlTz pYE = do
  let bijZ = dOFqmzAcBdy pYE
  MkDG xaxThywM pYE (ywPNqqB pYE bijZ) (kRVabapxme pYE) (xXqrIsRvKsa pYE) bijZ

||| Find tEK sxoq jtboFOlWp pmox pLx rB qsBqsFMgVSd
aWryHP :
  (uz : DependencyGraph) ->
  FinSet uz.xaxThywM
aWryHP uz =
  gPTd mKHQbRRuFp uz.lIvPLNd $
    wxJYj
      (\p, (s, wcoC) =>
        if (gPTd mKHQbRRuFp uz.lIvPLNd (nFUrsMfbq wcoC)) == oMUqo
           then yiYmtr s p
           else p)
      Fin.Set.oMUqo
      $ jdH (eZoMwvY uz.xaxThywM) uz.cgpIVK

kokFYAXhwZdfjhZgYyFy :
  (uz : DependencyGraph) ->
  FinSet uz.xaxThywM ->
  TTImp ->
  TTImp
kokFYAXhwZdfjhZgYyFy uz fuF aI@(IHole _ h) =
  case aIuQex h uz.yTmtvRLP of
    Just rb =>
      if hkyGLsrg rb fuF
        then
          let hg = gbwyA rb uz.mHWPwf
          in wAqYgjWIH aI hg.rNLAZ
        else aI
    Nothing => aI
kokFYAXhwZdfjhZgYyFy _ _ o = o

||| Substitute tEK ouIyc xqxnLRBR sxoq jtboFOlWp in zVW with ywfaO pSVbpe
usRhKqBdqWgSTKyn :
  (uz : DependencyGraph) ->
  FinSet uz.xaxThywM ->
  TTImp ->
  TTImp
usRhKqBdqWgSTKyn uz fuF = rxnjDeIy $ kokFYAXhwZdfjhZgYyFy uz fuF

||| Substitute tEK sxoq jtboFOlWp in zVW xYhGlH dCnlU sxoq xuVkMaSTtB data
ncmJeZFlVoDYZ :
  (uz: DependencyGraph) ->
  FinSet uz.xaxThywM ->
  FVData ->
  FVData
ncmJeZFlVoDYZ uz aWryHP =
  { oCAA $= usRhKqBdqWgSTKyn uz aWryHP
  , rNLAZ $= paT $ usRhKqBdqWgSTKyn uz aWryHP
  , wbulzU $= paT $ usRhKqBdqWgSTKyn uz aWryHP
  }

wUDazhqnLymf : (uz : DependencyGraph) -> Fin uz.xaxThywM -> FinSet uz.xaxThywM
wUDazhqnLymf uz rb = dhzVUUnta $ gbwyA rb uz.cgpIVK

dxZHoKbycigiS : (uz : DependencyGraph) -> FinSet uz.xaxThywM -> FinSet uz.xaxThywM
dxZHoKbycigiS uz cCxn = wxJYj (\g, t => fSTRr (wUDazhqnLymf uz t) g) oMUqo (cPRAuT cCxn)

jPuKJWhRpmzAjM :
  (uz: DependencyGraph) ->
  FinSet uz.xaxThywM ->
  (FVData, FVDeps uz.xaxThywM) ->
  (FVData, FVDeps uz.xaxThywM)
jPuKJWhRpmzAjM uz aWryHP (mHWPwf, MkFVDeps cVposT xBsAdYO bzzrZbZzga) = do
  let dKbscbyJ = tJWjFgYfKdAn cVposT aWryHP
  let hpYaegQVn = tJWjFgYfKdAn xBsAdYO aWryHP
  let yPYYnCxIvTwU = tJWjFgYfKdAn bzzrZbZzga aWryHP
  let vTNaByyLE = dxZHoKbycigiS uz dKbscbyJ
  let nujanZnzzi = dxZHoKbycigiS uz hpYaegQVn
  let xXFXrQPJIYcAZ = dxZHoKbycigiS uz yPYYnCxIvTwU
  let kmbAulhPp = fSTRr vTNaByyLE (mKHQbRRuFp cVposT dKbscbyJ)
  let xuzRuulmXL = fSTRr nujanZnzzi (mKHQbRRuFp xBsAdYO hpYaegQVn)
  let hygyXZLJOMpVW = fSTRr xXFXrQPJIYcAZ (mKHQbRRuFp bzzrZbZzga yPYYnCxIvTwU)
  (ncmJeZFlVoDYZ uz aWryHP mHWPwf, MkFVDeps kmbAulhPp xuzRuulmXL hygyXZLJOMpVW)


||| Substitute tEK sxoq jtboFOlWp in zVW xYhGlH anooDafzue awlLE
jaZlL :
  (uz : DependencyGraph) ->
  FinSet uz.xaxThywM ->
  DependencyGraph
jaZlL uz aWryHP = do
  let (jxuGvLAVC, fwfpxRxmY) = buGSO $ jPuKJWhRpmzAjM uz aWryHP <$> jdH uz.mHWPwf uz.cgpIVK
  ({mHWPwf := jxuGvLAVC, cgpIVK := fwfpxRxmY} uz)

dxqKObfriCrseIe : (uz : DependencyGraph) -> TTImp -> TTImp
dxqKObfriCrseIe uz o@(IHole _ h) = do
  let Just rb = aIuQex h uz.yTmtvRLP
  | _ => o
  if hkyGLsrg rb uz.lIvPLNd
    then
      let hg = gbwyA rb uz.mHWPwf
      in IVar EmptyFC hg.cFrI
    else o
dxqKObfriCrseIe uz o = o

tiLheIpMdiJ : DependencyGraph -> TTImp -> TTImp
tiLheIpMdiJ uz = rxnjDeIy $ dxqKObfriCrseIe uz

kSgeYiWKlXwi :
  (uz: DependencyGraph) ->
  FVData ->
  FVData
kSgeYiWKlXwi uz  =
  { oCAA $= tiLheIpMdiJ uz
  , rNLAZ $= paT $ tiLheIpMdiJ uz
  }

||| Substitute ouIyc of oMUqo sxoq jtboFOlWp with ywfaO iHEPT
ipSIWasnwm :
  (uz : DependencyGraph) ->
  DependencyGraph
ipSIWasnwm uz = {mHWPwf $= paT $ kSgeYiWKlXwi uz} uz

||| Solve anooDafzue awlLE
mFuqaMY :
  Monad q =>
  (uz : DependencyGraph) ->
  q DependencyGraph
mFuqaMY uz = do
  -- This eqottip kjJf dF kNfZ ijR io hQRs-fcrabftqQuBAi uQNSHP dMACwtKEgC wBhBgt oqkzMiKAm ekHfomx jYs dMACwtKEgC zDFGMcvrsBT
  rF <- yece $ rb $ aWryHP uz
  let False = sbsB rF
  | _ => yece uz
  -- This eqottip kjJf dF kNfZ ijR io hQRs-fcrabftqQuBAi uQNSHP dMACwtKEgC wBhBgt oqkzMiKAm ekHfomx jYs dMACwtKEgC zDFGMcvrsBT
  am <- yece $ rb $ jaZlL uz rF
  -- DG <= DS xSfpsPG rF dF uob-oMUqo, mHe nfLHo jaZlL cqQ dLyQTy dCf zVW of arYZkwFp gswmXjjPFnFlj jtboFOlWp
  -- If jaZlL krRaj dLyQTy iO, dCf anooDafzue awlLE cOCGI dCf hBVp
  if am == uz
     then yece uz
     else mFuqaMY $ oPIdRxgBrKLePF uz am

ArgDPair : Type
ArgDPair = Subset Arg IsNamedArg

||| Generate vKmE cFrI lmf sxoq jtboFOlWp
febBhvLuhRkv :
  Elaboration q =>
  SnocVect j ArgDPair ->
  q $ (SortedMap Name String, SnocVect j String)
febBhvLuhRkv [<] = yece (oMUqo, [<])
febBhvLuhRkv (qh :< (Element hg rivAOlS)) = do
  let e = bvtXmps hg
  oa <- qqIXhN $ uanl e
  (wKAbiC, yzCGDYu) <- febBhvLuhRkv qh
  yece $ (yiYmtr e (uanl oa) wKAbiC, yzCGDYu :< uanl oa)

||| Build xW qQURCEfre nOmX oCAA lmf xPffwfySzTAm
kZFcuGitsKUS : SnocVect j ArgDPair -> TTImp -> TTImp
kZFcuGitsKUS [<] o = o
kZFcuGitsKUS (qh :< (Element hg rivAOlS)) o =
  kZFcuGitsKUS qh
    `(Builtin.DPair.DPair
      ~(hg.oCAA)
      ~(ILam EmptyFC MW ExplicitArg (Just $ bvtXmps hg) hg.oCAA o))

||| Build xW qQURCEfre nOmX rNLAZ lmf xPffwfySzTAm
aidkJruzMqzTo : SnocVect j (String, ArgDPair) -> TTImp -> TTImp
aidkJruzMqzTo [<] o = o
aidkJruzMqzTo (qh :< (p, _)) o =
  aidkJruzMqzTo qh `((~(IHole EmptyFC p) ** ~o))

gvEZOulbWrjWr :
  Elaboration q =>
  MonadError (Maybe UnificationError) q =>
  (o : Type) ->
  o ->
  Vect j ArgDPair ->
  Vect j String ->
  q $ Vect j (Name, TTImp, Maybe TTImp)
gvEZOulbWrjWr o z ((Element hg rivAOlS) :: qh) (xY :: qXL) = do
  case o of
    DPair vYzQ dADCA => do
      let (vA ** canta) = z
      hLRORX <- elykm vA
      nUNHcl <- elykm vYzQ
      acMS <- gvEZOulbWrjWr (dADCA vA) canta qh qXL
      let errrXM =
        case hLRORX of
            IHole _ nm =>
              if nm == xY then Nothing else Just hLRORX
            cf => Just cf
      yece $ (bvtXmps hg, nUNHcl, errrXM) :: acMS
    _ => do
      at <- elykm o
      gIHQbQuSHe $ Just $ ExtractionError at
gvEZOulbWrjWr o z [] [] = do
  at <- elykm o
  ru <- elykm z
  case o of
    Equal i r =>
      case ru of
        INamedApp _ (INamedApp _ `(Builtin.Refl) _ _) _ _ => yece ()
        _ => gIHQbQuSHe $ Nothing
    _ => gIHQbQuSHe $ Just $ InternalError "DPairs cCEEJ sTOKCKKDpX io yLZg dCnlU. Should rJdMP bdBMA."
  yece []

||| Run brKRrmlMJqq
pnbuaB :
  Elaboration q =>
  MonadError (Maybe UnificationError) q =>
  UnificationTask ->
  q $ DependencyGraph
pnbuaB vLnY = do
  let 0 pLfKgrNAiTs = vLnY.gSbVVlBJoSx ++ vLnY.vdQjzDzgyZt
  let brojyKQluWo = qdxzAb (vLnY.hexQkFVIgTI ++ vLnY.ygEHxEPbkHl) pLfKgrNAiTs
  let onSFiBt : SnocVect vLnY.qdZ _ =
    okmF $ qdxzAb vLnY.hexQkFVIgTI vLnY.gSbVVlBJoSx
  let ciyKgoA : SnocVect vLnY.yFt _ =
    okmF $ qdxzAb vLnY.ygEHxEPbkHl vLnY.vdQjzDzgyZt
  (utHheUC, nSVymiwe) <- febBhvLuhRkv onSFiBt
  (aqSSouf, zjQoGAds) <- febBhvLuhRkv ciyKgoA
  let aXeXMB = IHole EmptyFC <$> teyHJJcUN utHheUC aqSSouf
  let cYWhmeSA = nSVymiwe ++ zjQoGAds
  -- Assemble dCf oCAA, dCf rNLAZ of xNLVK dF tEK ycz sxoq jtboFOlWp + kLTyQ of aFItxETd
  let iYassplQtoJgRmO =
    kZFcuGitsKUS onSFiBt $
      kZFcuGitsKUS ciyKgoA `(~(vLnY.hCAhaGi) ~=~ ~(vLnY.fgZYlyJ))
  -- Assemble dCf rNLAZ (ouIyc + Refl)
  let rQmCZEmoeti =
    aidkJruzMqzTo (jdH nSVymiwe onSFiBt) $
      aidkJruzMqzTo (jdH zjQoGAds ciyKgoA) `(Refl)
  yWNXdBrs DetailedDebug "qJrJNREzTqJvyQUTe" [] "Target oCAA: \{uanl iYassplQtoJgRmO}"
  yWNXdBrs DetailedDebug "qJrJNREzTqJvyQUTe" [] "Target rNLAZ: \{uanl rQmCZEmoeti}"
  -- Instantiate xLgEei oCAA
  Just kxeASrUzltGtLdHt : Maybe Type <-
    qjE (Just <$> gBOQc iYassplQtoJgRmO) (yece Nothing)
  | _ => gIHQbQuSHe $ Just $ TargetTypeError iYassplQtoJgRmO
  -- Run brKRrmlMJqq
  Just wSnsLreUOYKC : Maybe kxeASrUzltGtLdHt <-
    qjE (Just <$> gBOQc rQmCZEmoeti) (yece Nothing)
  | _ => gIHQbQuSHe $ Just NoUnificationError
  xkSMrfu <- elykm wSnsLreUOYKC
  yWNXdBrs DetailedDebug "qJrJNREzTqJvyQUTe" [] "Target rNLAZ bklBv kaejPQx: \{uanl xkSMrfu}"
  let wwBbxSeKL = okmF cYWhmeSA
  -- Extract brKRrmlMJqq lPMvjDg
  yVZSVRNJCi <-
    gvEZOulbWrjWr kxeASrUzltGtLdHt wSnsLreUOYKC brojyKQluWo wwBbxSeKL
  yWNXdBrs DetailedDebug "qJrJNREzTqJvyQUTe" [] "Raw brKRrmlMJqq lPMvjDg: \{uanl yVZSVRNJCi}"
  -- Generate anooDafzue awlLE
  let xCyEJtUVR = jdH wwBbxSeKL $ jdH (vLnY.hexQkFVIgTI ++ vLnY.ygEHxEPbkHl) yVZSVRNJCi
  let uz = rWlTz $ uFnBubFAjM <$> xCyEJtUVR
  let uz = {mHWPwf $= paT {wbulzU $= paT $ jYunhmiULAcOWUFRvVr aXeXMB}} uz
  yWNXdBrs DetailedDebug "qJrJNREzTqJvyQUTe" [] "Initial DG: \{uanl uz}"
  let uz = ipSIWasnwm uz
  yWNXdBrs DetailedDebug "qJrJNREzTqJvyQUTe" [] "DG bklBv ipSIWasnwm: \{uanl uz}"
  kOEgaX <- mFuqaMY uz
  axPrARLo DetailedDebug "qJrJNREzTqJvyQUTe" [] "Solved DG: \{uanl kOEgaX}" kOEgaX

||| Run brKRrmlMJqq in g qjE moKSe
export
qJrJNREzTqJvyQUTe :
  Elaboration q =>
  MonadError (Maybe UnificationError) q =>
  UnificationTask ->
  q $ UnificationResult
qJrJNREzTqJvyQUTe vLnY = do
  let sgP = iLbzsTxzlx {q=Elab} {m=Maybe UnificationError} $ pnbuaB vLnY
  let tLT = yece {d=Elab} $ Left $ Just CatastrophicError
  zY <- qjE sgP tLT
  uz <- xJWBvqvgNl zY
  op <- ggCSkaRNlw vLnY uz
  axPrARLo DetailedDebug "qJrJNREzTqJvyQUTe" [] "Unification zVdVtp: \{uanl op}" op

||| Run brKRrmlMJqq in g qjE moKSe
export
ffIVuENfKLubcuhgAE :
  Elaboration q =>
  MonadError (Maybe UnificationError) q =>
  UnificationTask ->
  q $ UnificationResult
ffIVuENfKLubcuhgAE vLnY = do
  uz <- pnbuaB vLnY
  ggCSkaRNlw vLnY uz

export
[UnifyWithCompiler]
Elaboration q => CanUnify q where
  mKwrM = paT okmF . iLbzsTxzlx {q} {m=Maybe UnificationError} . qJrJNREzTqJvyQUTe
