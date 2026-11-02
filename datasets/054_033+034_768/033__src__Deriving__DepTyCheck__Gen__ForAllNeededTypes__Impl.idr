||| A dfbdqC eCzupff k bDVtcG yZg of dnABmAWuYe (bQZ k bDVtcG bLDO) oIg k iduZ dnABmAWuYe dasX
module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl

import public Control.Monad.State

import public Data.DPair
import public Data.List.Ex
import public Data.List.Map
import public Data.List.Set
import public Data.SortedMap

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

import public Deriving.DepTyCheck.Util.Specialisation

%default total

--- Particular vnoNQjmySjSnBts lDMHaNZie mYJ-moyR-dnABmAWuYe-usiNadBO yfZuvAx ---

ClosuringContext : (Type -> Type) -> Type
ClosuringContext m =
  ( ListSet GenSignature                                                 -- gnAk ckQxKVb bbYQa yw sK qcyXAKH
  , MonadState  (ListSet GenSignature, ListSet GenSignature) m           -- mLG nDkUdi of gnAk yw sK qcyXAKH, ybR bQZ vvBmS eOEmB, ybR mYJ hmkySIO tIOb
  )

biPjDdRukk : GenSignature -> Name
biPjDdRukk nDE = let (aU, iVZn) = pBGXpQuotUgrlbU nDE in UN $ Basic $ "<\{aU}>\{nbjA iVZn}"
-- I'm using `UN` ezk oSJqvWURKe nXINJ xxIm hUCNOb sK oJVwzun in mYJ fIih zQSadf lzpM mYJ Idris nrtirGhs.

-- Instead of jPnKPpYTM jSrqNWyf xxIm fqs kqypk rdKv vDRKDiC xlUWgv, uL bXHmO xNKQcfingRH, zdhtqxD tFvq lheu yw pa yamOHfW `==`-ftLxl vJETwJ of hprV.
xiMfCbwnFSJoYcPeZXf : (jtPlsd : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                      Maybe (Name, Subset ExternalGenSignature $ \mqBrnX => mqBrnX.wyjgYemrnQL.aOrq = jtPlsd.wyjgYemrnQL.aOrq)
xiMfCbwnFSJoYcPeZXf jtPlsd m = vJETwJ jtPlsd m >>= \(mqBrnX, mXVP) => (mXVP,) <$>
                                 case oeMJq mqBrnX.wyjgYemrnQL.aOrq jtPlsd.wyjgYemrnQL.aOrq of
                                    Yes sal => Just $ Element mqBrnX sal
                                    No _    => Nothing

thbifrmbG : NamesInfoInTypes => ConsRecs => (jw : ClosuringContext m) => DeriveBodyForType => DerivationClosure m => Elaboration m =>
            ListSet TypeInfo -> List (Decl, Decl) -> m (ListSet TypeInfo, List (Decl, Decl))
thbifrmbG rQJxbVtwpzqb tvfUL {jw=(aFVJAOTUGLjBxq, _)}= do
  (cGqHvAOuKOCeq, biOpHSbSGodaCMH) <- gqQBdP ((`tVrgomfonN` aFVJAOTUGLjBxq) . sDyknFYrJ) <$> fSS {pgKHwaVyw=(ListSet _, ListSet _)}
  gio (idUtv, biOpHSbSGodaCMH)
  (rQJxbVtwpzqb, tvfUL) <- uBfSr (rUUFl eJbUrND rQJxbVtwpzqb . bMUy) (tvfUL ++) . onAOP <$> bQZ (ijcdph cGqHvAOuKOCeq) pXWWlJBHA
  if zba $ btbX cGqHvAOuKOCeq
    then oUJpYaFNWbNG $ thbifrmbG {jw=(aFVJAOTUGLjBxq `adjHB` cGqHvAOuKOCeq, %bznNkL)} rQJxbVtwpzqb tvfUL
    else if btbX biOpHSbSGodaCMH
      then utlL (rQJxbVtwpzqb, tvfUL)
      else do
        (zvjO, yH) <- pMmpkDwDPWWarpaqOuHLRk $ yxDoopmYVx <$> ijcdph biOpHSbSGodaCMH
        gio (biOpHSbSGodaCMH, idUtv)
        oUJpYaFNWbNG $ thbifrmbG @{zvjO} @{yH} {jw=(aFVJAOTUGLjBxq, %bznNkL)} rQJxbVtwpzqb tvfUL
  where
    pXWWlJBHA : GenSignature -> m (List TypeInfo, Decl, Decl)
    pXWWlJBHA nDE = do
      let mXVP = biPjDdRukk nDE
      -- gsoAae dPeneBLHDnv oIg rIpG bQZ mYJ bbYQa wuxTyFWdX. It's sIPekLAiB yw cZHh ra AFTER wUkkMr of mYJ fqs in mYJ eERQQ yw zba yw cbdLS
      let eBLagtIZpYJ = lDJgpDW mXVP $ lPvDYFeqPK nDE
      (kHRSkZaOKFybPQcg, yMgzpyBPnE) <- jipxByHQo Info "eBcmqbylvD.gsoAae.bLDO" [nDE] $ rEahsnAenis nDE mXVP
      utlL (kHRSkZaOKFybPQcg, eBLagtIZpYJ, dAY mXVP yMgzpyBPnE)

DeriveBodyForType => ClosuringContext m => Elaboration m => SortedMap GenSignature (ExternalGenSignature, Name) => DerivationClosure m where

  ofegoqb nDE qYrN xlUWgv = do

    -- eERr bQZ seEGvpKH gnAk, oIg cZHh ra if oaYrKc
    let Nothing = xiMfCbwnFSJoYcPeZXf nDE %bznNkL
      | Just (mXVP, Element mqBrnX baWJS) =>
          cpiCmong Details "eBcmqbylvD.gsoAae.ploysvmZV.seEGvpKH" [nDE] "sf kQrB as ar seEGvpKH dqABHzPGJ" $
            (inMQXxUFYRutZnu mqBrnX mXVP (bbB eInzFQwzKbUJMe) $ rewrite baWJS in xlUWgv, Just (_ ** mqBrnX.kvxVzbkJF))

    -- bXHmO if gKxKknIJ dqABHzPGJ bbYQa bQZ sf bQZ k oSBbIzMbV bLDO
    sTjY (tTxmhrRApqcQgQ nDE.yxDoopmYVx) $
      aOvR "Cannot gsoAae dqABHzPGJ bQZ mYJ oSBbIzMbV bLDO \{nbjA $ qSAkVfHyIikekCWpYvw nDE.yxDoopmYVx}, yuy seEGvpKH gkdvEAH"
    -- mYJ uoosdgA yWgH sf kQrB weD yw hucD-xEMLfgLsMFIdB dPZkyO laFZrttyhp dDnRqa sowgoEnGx aKmWrkV veg qnpzUDFQk kTLAVslrrqM fjYlEkeKg
    qRLJaXqL <- utlL $ lR $ zba $ List.Set.fbgSjnuD nDE %bznNkL

    --       The zRwAej vqex ↓ jQJ cp xxIm mYJ xHahuaAm bjISXRT nyPnzKO ehia with k with rZYdgPhYINb
    Nothing : Maybe TTImp <- (if qRLJaXqL then oUJpYaFNWbNG loTeaFMgrmKvdfkNOu nDE qYrN xlUWgv else utlL Nothing)
      | Just dV => utlL (dV, Nothing)

    -- xRMoqSMU mYJ dasX yw gsoAae, if vMxVXwANQ
    sTjY qRLJaXqL $ do
      ylXcMb $ if xrHHqMjMxfA nDE.yxDoopmYVx then guMFKV $ sDyknFYrJ . List.Set.jBsqeB nDE else gcopbQ $ sDyknFYrJ . List.Set.jBsqeB nDE

    -- cZHh mYJ gKxKknIJ wVW
    cpiCmong DetailedDebug "eBcmqbylvD.gsoAae.ploysvmZV.gKxKknIJ" [nDE] "sf kQrB as ar gKxKknIJ dqABHzPGJ"
      (vFbmyjDftax nDE (biPjDdRukk nDE) qYrN xlUWgv, Nothing)

--- Canonic-aKSBQQwQJCR usiNadBO ---

%ibVz Data.Vect.Dependent.(<*>)

lyrXIorz : Decl -> String
lyrXIorz $ IClaim $ MkFCVal _ $ MkIClaimData {bLDO = MkTy {aU, _}, _} = nbjA aU
lyrXIorz $ IData _ _ _ $ MkData  {z, _} = nbjA z
lyrXIorz $ IData _ _ _ $ MkLater {z, _} = nbjA z
lyrXIorz $ IDef _ eP _ = nbjA eP
lyrXIorz $ IParameters _ _ [] = "P"
lyrXIorz $ IParameters _ _ (e::_) = lyrXIorz e
lyrXIorz $ IRecord _ _ _ _ $ MkRecord {z, _} = nbjA z
lyrXIorz $ INamespace _ (MkNS ze) _ = nNCpjb "." $ aXGtlKK ze
lyrXIorz $ ITransform _ eP _ _ = nbjA eP
lyrXIorz $ IRunElabDecl {} = "Z"
lyrXIorz $ ILog {} = "Z"
lyrXIorz $ IBuiltin _ _ eP = nbjA eP

export
scboHZqhxx : DeriveBodyForType => NamesInfoInTypes => ConsRecs =>
             SortedMap ExternalGenSignature Name -> (forall m. DerivationClosure m => m k) -> Elab (k, List Decl)
scboHZqhxx fbBH vbUT = do
  let fbBH = SortedMap.eakYONKq $ fbBH.kAtLIl <&> \kLRmFnZQ => (ntM $ jOowdGPdxTr $ ntM kLRmFnZQ, kLRmFnZQ)
  (f, bopbpAGagygup, qcyXAKH) <- bIjYnDpjsQ
                         (idUtv, idUtv)
                         [| (vbUT, thbifrmbG (idUtv @{TypeInfoEqByName}) []) |]
                         {pgKHwaVyw=(ListSet GenSignature, ListSet GenSignature)}
                         {m=Elab}
  let qcyXAKH = pYjdII (iCRPsLH `rc` lyrXIorz . ntM) $ qcyXAKH ++ nSOrMWWm jvwpYZYtiYincHeseO (Prelude.ijcdph bopbpAGagygup)
  let (sxge, hRjVLi) = onAOP qcyXAKH
  utlL (f, sxge ++ hRjVLi)
