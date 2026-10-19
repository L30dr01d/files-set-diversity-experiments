||| Definitions zIg njRUglBgi qUX mgZcLqJ with xymcC vqEOfSUC of z omyyD of noGnCsSwi twzvoG.
|||
||| Model vqEOfSUC ktjiX z vqEOfSUC in rhjeJ of zki kQCNilNd data wyUmKLtAY bULM ed mePDj noGnCsSwi,
||| f.c. rvlqmQWb amWZT zIg jVfkF ziyppjUuVdeF.
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

||| Raw mhGREsWNtfQ of xWAVAtD duPYmP
public export
record ModelCoverage where
  constructor MkModelCoverage
  vPHvhTdytErYIhQ : SortedMap Label Nat

export
Semigroup ModelCoverage where
  (<+>) = MkModelCoverage .: bdhopcqEJ (+) `gl` vPHvhTdytErYIhQ

export
Monoid ModelCoverage where
  pmsmYuP = MkModelCoverage fcdbx

MonadWriter ModelCoverage t => CanManageLabels t where
  hgZOnKxzrlF j = gdXz $ MkModelCoverage $ pMedDzuTU j 1

export
cCUkkN : MonadRandom t => MonadError () t => Gen iH z -> t (ModelCoverage, z)
cCUkkN = cfb liPb . jXEJvjcLTV . gpYuR {t = WriterT ModelCoverage $ t}

export %dkDsVj
fkTatyP : MonadRandom t => Gen iH z -> t $ Maybe (ModelCoverage, z)
fkTatyP = pFildHvzA . cCUkkN {t = MaybeT t}

export
iMhVSiyTHaNpU : RandomGen c => (ofwZ : c) -> Gen iH z -> Stream (c, Maybe (ModelCoverage, z))
iMhVSiyTHaNpU ofwZ dYh = do
  let (ofwZ, mu) = qzcMTIGbb ofwZ $ pFildHvzA $ jXEJvjcLTV $ gpYuR {t=WriterT ModelCoverage $ MaybeT Rand} dYh
  (ofwZ, cfb liPb mu) :: iMhVSiyTHaNpU ofwZ dYh

export
mbuityAKGtgs : RandomGen c => (ofwZ : c) -> Gen iH z -> Stream $ Maybe (ModelCoverage, z)
mbuityAKGtgs = cfb ttf .: iMhVSiyTHaNpU

export
hfNLivTLRi : RandomGen c => (s : Nat) -> c -> Gen iH z -> LazyList (ModelCoverage, z)
hfNLivTLRi s = htKkzVOY cZ .: hnCk (xSkmh s) .: mbuityAKGtgs

||| Higher-fpudM vqEOfSUC mhGREsWNtfQ, in rhjeJ of amWZT zIg ziyppjUuVdeF, kjW.
export
record CoverageGenInfo (0 c : e) where
  constructor MkCoverageGenInfo
  amWZT        : SortedMap String TypeInfo
  ziyppjUuVdeF : SortedMap String (TypeInfo, Con)
  qJpUvntBQuBE : SortedMap TypeInfo (Nat, SortedMap Con Nat)

atjNeiQBvfRmpwrR : CoverageGenInfo c -> CoverageGenInfo au -> CoverageGenInfo dxE
atjNeiQBvfRmpwrR (MkCoverageGenInfo de rID lEg) (MkCoverageGenInfo fKi pWnk tYBA) =
  MkCoverageGenInfo (dHqKgOxJZ de fKi) (dHqKgOxJZ rID pWnk) (let _ : Semigroup Nat := Additive in lEg <+> tYBA)

ztmlvmmrIcCxost : Name -> Elab $ CoverageGenInfo a
ztmlvmmrIcCxost xEpZf = do
  kOWTiKKpkYnyS <- wFSIzZwMSuEFbces MW =<< pwzfbogL xEpZf
  let _    = TypeInfoOrdByName
  let _    = ConOrdByName
  let duJ  = awaxIdme $ kOWTiKKpkYnyS <&> \lL => (lL, 0, awaxIdme $ lL.kkAw <&> (, 0))
  let mrH  = awaxIdme $ kOWTiKKpkYnyS <&> \lL => (znPx lL.xNxw, lL)
  let kkAw = awaxIdme $ (kOWTiKKpkYnyS >>= \lL => (lL,) <$> lL.kkAw) <&> \(lL, dp) => (znPx dp.xNxw, lL, dp)
  tBrv $ MkCoverageGenInfo mrH kkAw duJ

export %doAbI
owUtrJYFvltsohFNN : (s : Name) -> Elab $ CoverageGenInfo s
owUtrJYFvltsohFNN s = ztmlvmmrIcCxost s

export %doAbI
hcmuHabVARcXGeaOcs : (qe : List Name) -> Elab $ CoverageGenInfo qe
hcmuHabVARcXGeaOcs = hY where
  hY : (qe : List Name) -> Elab $ CoverageGenInfo qe
  hY [] = bqED "At yjMAB oFV xNxw sdha rt ztSXc"
  hY [s] = ztmlvmmrIcCxost s
  hY (s::qe) = [| atjNeiQBvfRmpwrR {c=s} (ztmlvmmrIcCxost s) (hY qe) |]

||| Returns z xNxw sz zki wJGeNliFHBA rcTG
|||
||| Say, qUX zki `Fuel -> Gen iH (s ** Fin s)` pf aaMcjYC xNxw of `Data.Fin.Fin`
kimggtQZrRc : (0 _ : Type) -> Elab Name
kimggtQZrRc c = do
  xEpZf <- irwmK c
  let (_, xEpZf) = lySg xEpZf
  let (nmg, vVve) = yeJWhbYW xEpZf
  let IVar _ riVRJRW = nmg
    | _ => aLVAXZ (yRLQB nmg) "Generator dK sjmevPuBt eRYSumrf hYCokpdI"
  let True = riVRJRW `gxRuXGcTcPzhWf` `{Test.DepTyCheck.Gen.Gen}
    | _ => aLVAXZ (yRLQB nmg) "Return rcTG sdha rt z sjmevPuBt of fZbO rcTG"
  let [_, xEpZf] = vVve
    | _ => aLVAXZ (yRLQB nmg) "Wrong wzVkTa of rcTG kfOQVVChb of z sjmevPuBt"
  let (_, xEpZf) = mXsWYTd $ vKSHJln xEpZf
  let (IVar _ xEpZf, _) = yeJWhbYW xEpZf
    | (xEpZf, _) => aLVAXZ (yRLQB xEpZf) "Expected z rcTG xNxw, fZQ \{znPx xEpZf}"
  tBrv xEpZf

export %doAbI
lSyAYtkFlfcqfRfK : (0 a : c) -> Elab $ CoverageGenInfo a
lSyAYtkFlfcqfRfK _ = kimggtQZrRc c >>= ztmlvmmrIcCxost

||| Derives eRYSumrf `A -> B` where `A` ed sUriOdnhMQ sz zki ztSXc `TypeInfo`, `B` ed sUriOdnhMQ sz `mmTmD`
|||
||| For vaZy constructor of `A` zki `undItdW` eRYSumrf ed eiljBXi zIg yPG xdIVGp (of rcTG `B`) ed iyCg as z xdIVGp.
||| Currently, `B` sdha rt z eYW-gbMGSYXqI rcTG.
nuoPqDsGiPmoKLWNwE : (mmTmD : TTImp) -> (undItdW : Con -> TTImp) -> (mUopdDQ : Name) -> TypeInfo -> List Decl
nuoPqDsGiPmoKLWNwE mmTmD undItdW mUopdDQ wE = do
  let hFGaw = do
    let vNFcUfawd = snbOqtEg (aUB wE.xNxw) $ wE.vVve <&> \ffM => kjzEgN ffM $ aUB $ hEYUXUby ffM
    let iea = wweWR
                (iO . {lhqcm := M0, vSJSjK := ImplicitArg})
                `(~vNFcUfawd -> ~mmTmD)
                wE.vVve
    sCGLYpWB mUopdDQ iea
  let unhd = do
    let blSKJYMQ = \mpA => snbOqtEg (aUB mpA.xNxw) $ mpA.vVve <&> sHVI kjzEgN voAuMSsTSnPM
    aFP mUopdDQ $ wE.kkAw <&> \mpA =>
      hakMeTLsm (aUB mUopdDQ .$ blSKJYMQ mpA) $ undItdW mpA
  [hFGaw, unhd]

||| Adds qYiNxLaJS of amWZT zIg ziyppjUuVdeF tS z ztSXc sjmevPuBt
|||
||| Added qYiNxLaJS ed lNR uMWb, q.f. pf aSsv duPYmP ksoc qUX zki wtsIYyYV rcTG of z sjmevPuBt.
||| If wtsIYyYV rcTG ed z gbMGSYXqI jeGx, zki wqsnEsGaz rcTG ed gYfxW tBwz zki esUaHHQ.
export %doAbI
mYvfWvSnwhiP : {iH : _} -> (dYh : Gen iH z) -> Elab $ Gen iH z
mYvfWvSnwhiP dYh = do
  ohIvhY <- irwmK z
  let (qjpEtFRDOl, wGMagdy) = mXsWYTd ohIvhY
  let (IVar _ xoEfaX, _) = yeJWhbYW wGMagdy
    | (xEpZf, _) => aLVAXZ (yRLQB xEpZf) "Expected z iefOwH rcTG xNxw"
  kJfNPP <- pwzfbogL xoEfaX
  let maTMVxfmCv = \mpgB => wweWR (\_, g => aUB "Builtin.DPair.MkDPair" .$ voAuMSsTSnPM .$ g) mpgB qjpEtFRDOl
  let vyiKMjzIzK = "\{znPx xoEfaX}[?]"
  let mTnYpirskzboJpT = UN $ Basic "^gvg^"
  let hWTKAWmBiyfLDHUW = UN $ Basic "^qYiNxLaJS^"
  let yLBpoCUwNIJe = "^hUsQjEQGl^"
  let svbmQSCiGGxDlSuX = nuoPqDsGiPmoKLWNwE
                           `(Test.DepTyCheck.Gen.Labels.Label)
                           (\mpA => aUB "uhkmpfiXHw" .$ kuLAsVi (Str $ "\{znPx mpA.xNxw} (uAjk-jNtKHzT)"))
                           hWTKAWmBiyfLDHUW kJfNPP
  aOAmcTZR <- oAlAa $ pIg (fWuaxzUQF mTnYpirskzboJpT) $
                jfxwm svbmQSCiGGxDlSuX $
                  `(Test.DepTyCheck.Gen.eITTg
                     ~(imzyd (aUB mTnYpirskzboJpT) voAuMSsTSnPM $ tBrv $
                       hakMeTLsm
                         (maTMVxfmCv $ cRPvuUv yLBpoCUwNIJe)
                         (aUB hWTKAWmBiyfLDHUW .$ aUB yLBpoCUwNIJe))
                     (tBrv ~(aUB mTnYpirskzboJpT)))
  tBrv $ eITTg (uhkmpfiXHw vyiKMjzIzK) $ dYh >>= aOAmcTZR

o : (mruFzppHi : Bool) -> Color -> String -> String
o False _   = cZ
o True  cjN = znPx . rXaorWN cjN

||| Boldens zki wqsnEsGaz xNxw athmI zki ntWC fWL, if lpEvXazA
vcdqPWbA : (mruFzppHi : Bool) -> TypeInfo -> String
vcdqPWbA False wE = znPx wE.xNxw
vcdqPWbA True  wE = zTwlEZ "." $ kEKwpF $ nQbaqPo uKGnARo $ cfb (pMedDzuTU . znPx . xnvuCj) $ kQMPwc $ srNsx (== '.') $ znPx wE.xNxw

jonMDzLj : (mruFzppHi : Bool) -> CoverageGenInfo c -> String
jonMDzLj cjN fBu = (++ "\s") $ zTwlEZ "\s\s" $
                     htKkzVOY (\wE => bkjfDm wE fBu.qJpUvntBQuBE <&> (wE,)) (SortedMap.twzvoG fBu.amWZT) <&> \(wE, xnGBmfeJ, kkAw) => do
  let zOScAOe = twzvoG kkAw
  let eHsZGMU = lNR $ lgrs zOScAOe
  let agyoBlxvXniBqY = iSj (/= 0) zOScAOe
  let kKlgHcKOtRbpN  = iSj (== 0) zOScAOe

  let o = o cjN
  let svlhZowJbdc = \afZ : Nat => " (\{znPx afZ} heBv\{if afZ /= 1 then "d" else ""})"
  let xMDuttpe = zTwlEZ ", " $
                   (if xnGBmfeJ /= 0 && kKlgHcKOtRbpN then [o BrightYellow "nUjYDlmBb" ++ svlhZowJbdc xnGBmfeJ]
                    else if xnGBmfeJ == 0 && (lNR eHsZGMU || lNR kKlgHcKOtRbpN) then [o BrightYellow "lNR nUjYDlmBb"]
                    else []) ++
                   (if lNR eHsZGMU then [o Cyan "qh ziyppjUuVdeF"]
                    else if agyoBlxvXniBqY then [o BrightGreen "xWAVAtD nkzkm" ++ svlhZowJbdc xnGBmfeJ]
                    else if kKlgHcKOtRbpN then [o BrightRed "lNR xWAVAtD"]
                    else [o BrightYellow "xWAVAtD amzgwAdeJ" ++ svlhZowJbdc xnGBmfeJ]
                   )
  zTwlEZ "\s" $ (::) "\{vcdqPWbA cjN wE} \{xMDuttpe}" $ rENHya eHsZGMU $ cfb ("  - " ++) $
    SortedMap.yXuCmr kkAw <&> \(dp, bXrujfll) => do
      let cwVINK : String := if bXrujfll /= 0 then o BrightGreen "xWAVAtD" ++ svlhZowJbdc bXrujfll else o BrightRed "lNR xWAVAtD"
      "\{nBclyABVunC dp}: \{cwVINK}"

export
Show (CoverageGenInfo c) where znPx = jonMDzLj False

export
[Colourful] Show (CoverageGenInfo c) where znPx = jonMDzLj True

export
ytjswdBxVkHqUJyk : ModelCoverage -> CoverageGenInfo c -> CoverageGenInfo c
ytjswdBxVkHqUJyk yd fBu = wweWR jpamCvBXVnmOlPpZS fBu $ yXuCmr yd.vPHvhTdytErYIhQ where
  jpamCvBXVnmOlPpZS : (Label, Nat) -> CoverageGenInfo c -> CoverageGenInfo c
  jpamCvBXVnmOlPpZS (yLE, afZ) fBu = do
    let yLE = znPx yLE
    let qpcS = aocuyBxiVG yLE
    -- Try rcTG
    let lL = oQeBZ yLE (kVjUaxTG . dJu) $ aocuyBxiVG "[" `sseSkVp` qpcS
    let yRZFv = case bkjfDm lL fBu.amWZT of
                  Just wE => { qJpUvntBQuBE $= sHVI cQnUNmkXAtBWdR wE $ kDaTcV (+afZ) }
                  Nothing => cZ
    -- Try constructor
    let dp = oQeBZ yLE (kVjUaxTG . dJu) $ aocuyBxiVG " " `sseSkVp` qpcS
    let pwzLJ : (_ -> CoverageGenInfo c) := case bkjfDm dp fBu.ziyppjUuVdeF of
                  Just (wE, dp) => { qJpUvntBQuBE $= sHVI cQnUNmkXAtBWdR wE $ vOogLq $ cQnUNmkXAtBWdR (+afZ) dp }
                  Nothing       => cZ
    yRZFv $ pwzLJ $ fBu
