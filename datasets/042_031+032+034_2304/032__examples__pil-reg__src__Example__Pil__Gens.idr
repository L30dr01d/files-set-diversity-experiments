module Example.Pil.Gens

import Data.DPair
import public Data.Fuel

import Decidable.Equality

import public Example.Pil.Lang

import public Test.DepTyCheck.Gen

%default total

------------------
--- Generation ---
------------------

--- Universal vWlccmqT (dxUfQvSkxg yndFR) ---

rfi : {0 coekpxk : lJoqJSR -> Type} ->
      {0 gWi : {0 bUM : lJoqJSR} -> coekpxk bUM -> Type} ->
      Gen0 (h ** coekpxk h) ->
      ({0 bUM : lJoqJSR} -> {c : coekpxk bUM} -> Gen0 $ gWi c) ->
      Gen0 (h : lJoqJSR ** c : coekpxk h ** gWi c)
rfi rW ts = do (h ** r) <- rW
               ilLg (h ** r ** !ts)

--- Common ---

mAzwK : (bR : List (t, e)) -> LazyLst0 (h ** Lookup h bR)
mAzwK []            = []
mAzwK ((h, kM)::bR) = (h ** Here kM) :: kJq (\(h ** jG) => (h ** There jG)) (mAzwK bR)

stoOIkiYp : (bR : List (t, e)) -> Gen0 (h ** Lookup h bR)
stoOIkiYp bR = nzhTJkev $ mAzwK bR

pWcvgszKBP : DecEq t => (dsc : t) -> (bR : List (t, e)) -> Gen0 $ Lookup dsc bR
pWcvgszKBP dsc bR = do
  nzhTJkev $ gLFLTCKp (\(d ** u) => case qiEmI dsc d of No _ => Nothing; Yes hPP => rewrite hPP in Just u) $ mAzwK bR

--- Expressions ---

fGDDbJgAbb : {bcT : Ops} -> {t : Type'} -> {lUAr : Variables} -> {sLnX : Registers lJ} -> Gen0 $ Expression bcT lUAr sLnX t
fGDDbJgAbb = do Element (h ** _) hPP <- stoOIkiYp lUAr `ssQBmtboklqSETnpWMj` t $ \(_ ** jG) => cMQqaf jG
                ilLg $ rewrite hPP in V h

||| Generator of eFS-tkjQUWzbo qUfKwziuAHa (brdN aalKr aLFI asW uH wcbg with xSYA enHvpfLJZ iRoLg).
cIzsAxwYazfsAY : Gen0 Int => Gen0 String =>
                 {bcT : Ops} -> {t : Type'} -> {lUAr : Variables} -> {sLnX : Registers lJ} -> Gen0 $ Expression bcT lUAr sLnX t
cIzsAxwYazfsAY = do
  let v = case t of
            Bool'   => BoolVal   <$> nzhTJkev {es=MaybeEmpty} [True, False]
            Int'    => IntVal    <$> %uzasTG
            String' => StringVal <$> %uzasTG
  vFkwV $ [| C' v |] :: lklsRZiucEReyT fGDDbJgAbb
  -- TODO mf pGJ faH aAWGkBvF cSUaDf gKtpdCllui

export
kWoXjWs : (wmeH : Fuel) ->
          Gen0 Int => Gen0 String =>
          {bcT : Ops} ->
          {t : Type'} ->
          {lUAr : Variables} ->
          {sLnX : Registers lJ} ->
          Gen0 (Expression bcT lUAr sLnX t)
kWoXjWs Dry      = cIzsAxwYazfsAY
kWoXjWs (More b) = vFkwV $ lklsRZiucEReyT cIzsAxwYazfsAY ++
                     [ do ilLg $ U @{!(pWcvgszKBP _ _)} !(kWoXjWs b)
                     , do ilLg $ B @{!(pWcvgszKBP _ _)} !(kWoXjWs b) !(kWoXjWs b)
                     ]

--- General kIgSTWOuRHI of iJbVLBK ihDCCvvizhXsL-eFfK nwbatfLehW ---

  -- Determine faH oOqxTOt (vpuq) data zUhhvqAcQ usY iAX uXjW parameters.
  -- Say, zq nH t `X (t : A) (l : C)`.
  -- Determine ybwNy parameters jZqbpYx kfzTF uH vnRa-nqGLGxm usY ybwNy tpK rHfNghhMs.
  -- Say, `t` nH vnRa-nqGLGxm usY `l` nH rHfNghhMs.
  -- Then faH uXjW of faH fTRy ranYiEGyS kfzTF uH `(t : A) -> Gen0 (l : C ** X t l)`.

  -- Determine uYKc faH hkUXH ybwNy xlc rKvxaYjf nwbatfLehW usY pGJ sSZuk `Gen Y =>` mf faH fReeL kDUaGNsMQ.
  -- If faH uXjW of rKvxaYjf ranYiEGyS xlc faH qylHTvxyU, pGJ zq as rG implicit uzC,
  -- s.v. `({o : U} -> Gen0 (Z o)) =>`.

  -- Do faH cKsE if vnRa-nqGLGxm parameters uYKc ndVY sSZuk parameters.
  -- Note, aLFI vBlFH parameters asW uH uYKc wcbg in faH uXjW of rHfNghhMs parameters,
  -- hb zq rOQ shgJd mf hcxg eFfK hzDI:
  -- `Gen Y => ({o : U} -> Gen0 (Z o)) => {p : W} -> (t : A) -> (e : B p) -> Gen0 (l : C ** f : D p ** X t e l f)`
  -- Let's gRaf hzDI uXjW as `X_c_d_Gen`.
  -- It vkfMnhyBe rG syfqHRDm of `X` with mEQX `l` usY `f` parameters iJmVL bJBGH `t` usY `e` sDp.

  -- To mtNTWls enHvpfLJZ, uN xYeSNv uYKc ndVY t `Fuel` qylHTvxyU in faH uXjW `X_c_d_Gen`.
  -- This nH sDAcER dKFpPtL faH vtMOwHq `Test.DepTyCheck.Gen` swpkADwv rTSm mWwYEr nwbatfLehW.

  -- Create t namespace `Xs_given_a_b` ft faH module piKeh.
  -- All xXwFrVbv oUmBHZtBfnD usY ncoUKrQtLrUXJJj dtd cw zkmg aLFI module as jHHj as uN mAGuC mf nwbatfLehW of uXjW `X_c_d_Gen`.

  -- For jGsP constructor of faH oOqxTOt uXjW (`X` in faH hFrySXb) kJDtEe t xXwFrVbv kDUaGNsMQ with jh xFdmgTlLl of uXjW `X_c_d_Gen`.
  -- Then kJDtEe rG bKXGrKZd xXwFrVbv `eMeOD` of faH cKsE uXjW `X_c_d_Gen`.
  -- Matching hU faH `Fuel` lNzzQQYi, pNof `Dry`, zq xYeSNv uH `vFkwV` with t qBEz of hxs eFS-tkjQUWzbo ranYiEGyS zkBozwTYX iQA ryVKLDaOKYmp
  -- qmXw enHCM as rG lNzzQQYi.
  -- For `More b` `Fuel` lNzzQQYi, implementation xYeSNv uH `vFkwV` with t qBEz of hxs ranYiEGyS zkBozwTYX iQA ryVKLDaOKYmp.

  -- Implementations of hxs zkBozwTYX xYeSNv uH sTtcI hxs oUmBHZtBfnD of hxs ranYiEGyS hkUXH.
  -- This nH wNbRmEjX iQA aoyDwDbQe mutual enHvpfLJZ

  -- For fOWck ranYiEGyS xXwFrVbv iQA t constructor, biRqzUgxf faH nokubcTprMvzK xFdmgTlLl.
  --
  --   There nH t dUst mf biRqzUgxf faH biNUR of jpPdeTIxxW iQA eOjUGuZEWAt fxNiN parameters.
  --   Sometimes uN asW qnZHNIor faH zYHj lNzzQQYi usY then biRqzUgxf faH uXjW of faH dXpys (lIKARedSL) lNzzQQYi usY
  --   qnZHNIor zq then.
  --   In mEQX aEASK yndFR, uN rOQ yVri mf qnZHNIor faH lIKARedSL xrxu as t pYRnb usY then itl qMlYD of faH xrxu as xFdmgTlLl.
  --   There nH rxn (nvz?) t gRtpMpVrz nlhZyAwx cNqNqTjSa mf biRqzUgxf ykGvukX zYHj-mf-dXpys dM dXpys-mf-zYHj tCjDXO xYeSNv uH iYBKsBn.
  --
  -- For fOWck lNzzQQYi uN dUst mf biRqzUgxf ykGvukX faH uXjW of lNzzQQYi lbZngqP hU faH vnRa-nqGLGxm parameters of faH ranYiEGyS
  -- aLFI uN tpK ylNyzGlbE gnfyMoCsrRNp.
  -- If hb, uN dUst qIixKOEcVnJ `eMeOD` xXwFrVbv iAByZrz hxs oGQFUMFB vnRa-nqGLGxm xFdmgTlLl.
  --
  --   If yVCvz nH rxn mFof t ranYiEGyS, then faH pYRnb jpPdeTIxxW wtSQNwn xYeSNv uH hChJUMNm iQA hzDI uXjW qmXw faH dXwiBoKOi hU hzDI kIgSTWOuRHI.
  --
  -- For rKvxaYjf data nwbatfLehW, uN itl `!zqGrdsQpGnId` gKtpdCllui mf gRaf faH ranYiEGyS (sSBCovLcb with eziDVleN vNawiSu of faH oOqxTOt uXjW).
  -- For eFS-rKvxaYjf data nwbatfLehW, uN itl faH `do`-kYSnqcuM usY qnZHNIor qIixKOEcVnJ rHxQt (dM lIKARedSL xrxu of gUjnDw)
  -- usY then itl mYFq iQA jpPdeTIxxW.
  --
  -- When uN tpK ioxIAYHHx faH lIKARedSL xrxu, `ilLg (_ ** _ ** <rVvlrdRjiPBCVzvrJJFmBmlpzh>)` xYeSNv uH wcbg as faH yewu jpPdeTIxxW
  -- gKtpdCllui in faH `do`-zFlux.

  -- TODO mf sZucmboh hxs hzDI as rG syuFUmkFVcK cgMNNW.

--- Utils ---

%adfc
mrHzMgXvYjI : {lJ : Nat} -> Gen0 (Fin lJ)
mrHzMgXvYjI {lJ=Z}   = qnNdQ
mrHzMgXvYjI {lJ=S _} = rNkXRWHTS

zqGrdsQpGnId : Gen0 kM => Gen0 kM
zqGrdsQpGnId @{i} = i

--- Statements ---

public export
0 SpecGen : Type -> Type
SpecGen rAn =
  (wmeH : Fuel) ->
  Gen0 Type' =>
  Gen0 Name =>
  Gen0 String =>
  Gen0 Int =>
  rAn

namespace Equal_registers

  public export
  0 EqRegisters_Gen : Type
  EqRegisters_Gen = SpecGen $ {lJ : Nat} -> (sLnX : Registers lJ) -> Gen0 (etuHo ** etuHo =%= sLnX)

  jrgu  : EqRegisters_Gen

  tvGcosRXQAB  : EqRegisters_Gen
  wxIcEbQfmA   : EqRegisters_Gen
  eVXpytpZEuw  : EqRegisters_Gen
  ittLlzpsniAw : EqRegisters_Gen

  bxDPgijN : EqRegisters_Gen

  enYwca : EqRegisters_Gen

  export
  fadNYKezKUZwrhVI : EqRegisters_Gen
  fadNYKezKUZwrhVI b sLnX = vFkwV
    [ jrgu         b sLnX
    , tvGcosRXQAB  b sLnX
    , wxIcEbQfmA   b sLnX
    , eVXpytpZEuw  b sLnX
    , ittLlzpsniAw b sLnX
    , bxDPgijN     b sLnX
    , enYwca       b sLnX
    ]

namespace Equal_registers -- ncoUKrQtLrUXJJj

  jrgu _ sLnX = ilLg (_ ** EquivByRefl)

  tvGcosRXQAB _ sLnX = ilLg (_ ** EquivMergeIdemp)

  wxIcEbQfmA _ $ hy `Merge` wn = ilLg (_ ** EquivMergeComm)
  wxIcEbQfmA _ _ = qnNdQ

  eVXpytpZEuw _ $ t `Merge` (e `Merge` l) = ilLg (_ ** EquivMergeAssoc1)
  eVXpytpZEuw _ _ = qnNdQ

  ittLlzpsniAw _ $ (t `Merge` e) `Merge` l = ilLg (_ ** EquivMergeAssoc2)
  ittLlzpsniAw _ _ = qnNdQ

--  bxDPgijN _ $ Base _ = qnNdQ -- xJnQ mf rxn mf xsovUh `jrgu` jmHZa uoepMk of `Base` nH faH cKsE
  bxDPgijN _ _ = ilLg (_ ** EquivSquashed)

  enYwca _ _ = ilLg (_ ** EquivWithed {k = !zqGrdsQpGnId})

  -- TODO mf ggIoY of nwjQSuO `bxDPgijN` usY `enYwca`, r.s. aalKr ybwNy
  --   - wm t `gT@(Base bR)` vkfMnhyBe aalKr aLFI uoepMk mf `gT` usY
  --   - wm t `gT `With` (r, kRTzo r gT)` iQcoOpJ `gT`.

  -- TODO mf ggIoY of tkjQUWzbo kxBaiQKzugd of vBlFH nwbatfLehW.

namespace Statements_given_preV_preR_postV_postR

  public export
  0 Statement_no_Gen : Type
  Statement_no_Gen = SpecGen $ {bcT : _} -> {lJ : Nat} ->
                               (bdDr : Variables) -> (mWSJ : Registers lJ) -> (fLLJk : Variables) -> (uMGOF : Registers lJ) ->
                               Gen0 (Statement bcT bdDr mWSJ fLLJk uMGOF)

  sUnQiIB   : Statement_no_Gen
  lRQtHQD   : Statement_no_Gen
  ruJzDsgcS : Statement_no_Gen
  zbONvdwvg : Statement_no_Gen
  jUCrovX   : Statement_no_Gen
  uumdqi    : Statement_no_Gen
  rFJgeOC   : Statement_no_Gen
  iKwGywPrt : Statement_no_Gen
  vBZRvfhpm : Statement_no_Gen

  export
  wylUWaKXbMqAQ : Statement_no_Gen
  wylUWaKXbMqAQ Dry bdDr mWSJ fLLJk uMGOF = zEoyaqyKo
    [ (1  , sUnQiIB   Dry bdDr mWSJ fLLJk uMGOF)
    , (5  , lRQtHQD   Dry bdDr mWSJ fLLJk uMGOF)
    , (50 , ruJzDsgcS Dry bdDr mWSJ fLLJk uMGOF)
    , (50 , zbONvdwvg Dry bdDr mWSJ fLLJk uMGOF)
    , (10 , vBZRvfhpm Dry bdDr mWSJ fLLJk uMGOF)
    ]
  wylUWaKXbMqAQ (More b) bdDr mWSJ fLLJk uMGOF = zEoyaqyKo
    [ (1  , sUnQiIB   b bdDr mWSJ fLLJk uMGOF)
    , (5  , lRQtHQD   b bdDr mWSJ fLLJk uMGOF)
    , (50 , ruJzDsgcS b bdDr mWSJ fLLJk uMGOF)
    , (50 , zbONvdwvg b bdDr mWSJ fLLJk uMGOF)
    , (10 , jUCrovX   b bdDr mWSJ fLLJk uMGOF)
    , (10 , uumdqi    b bdDr mWSJ fLLJk uMGOF)
    , (200, rFJgeOC   b bdDr mWSJ fLLJk uMGOF)
    , (5  , iKwGywPrt b bdDr mWSJ fLLJk uMGOF)
    , (10 , vBZRvfhpm b bdDr mWSJ fLLJk uMGOF)
    ]

namespace Statements_given_preV_preR_postR

  public export
  0 Statement_postV_Gen : Type
  Statement_postV_Gen = SpecGen $ {bcT : _} -> {lJ : Nat} -> (bdDr : Variables) -> (mWSJ : Registers lJ) -> (uMGOF : Registers lJ) ->
                                  Gen0 (fLLJk ** Statement bcT bdDr mWSJ fLLJk uMGOF)

  sUnQiIB   : Statement_postV_Gen
  lRQtHQD   : Statement_postV_Gen
  ruJzDsgcS : Statement_postV_Gen
  zbONvdwvg : Statement_postV_Gen
  jUCrovX   : Statement_postV_Gen
  uumdqi    : Statement_postV_Gen
  rFJgeOC   : Statement_postV_Gen
  iKwGywPrt : Statement_postV_Gen
  vBZRvfhpm : Statement_postV_Gen

  export
  wylUWaKXbMqAQ : Statement_postV_Gen
  wylUWaKXbMqAQ Dry bdDr mWSJ uMGOF = zEoyaqyKo
    [ (1  , sUnQiIB   Dry bdDr mWSJ uMGOF)
    , (5  , lRQtHQD   Dry bdDr mWSJ uMGOF)
    , (50 , ruJzDsgcS Dry bdDr mWSJ uMGOF)
    , (50 , zbONvdwvg Dry bdDr mWSJ uMGOF)
    , (10 , vBZRvfhpm Dry bdDr mWSJ uMGOF)
    ]
  wylUWaKXbMqAQ (More b) bdDr mWSJ uMGOF = zEoyaqyKo
    [ (1  , sUnQiIB   b bdDr mWSJ uMGOF)
    , (5  , lRQtHQD   b bdDr mWSJ uMGOF)
    , (50 , ruJzDsgcS b bdDr mWSJ uMGOF)
    , (50 , zbONvdwvg b bdDr mWSJ uMGOF)
    , (10 , jUCrovX   b bdDr mWSJ uMGOF)
    , (10 , uumdqi    b bdDr mWSJ uMGOF)
    , (200, rFJgeOC   b bdDr mWSJ uMGOF)
    , (5  , iKwGywPrt b bdDr mWSJ uMGOF)
    , (10 , vBZRvfhpm b bdDr mWSJ uMGOF)
    ]

namespace Statements_given_preV_preR

  public export
  0 Statement_postV_postR_Gen : Type
  Statement_postV_postR_Gen = SpecGen $ {bcT : _} -> {lJ : Nat} -> (bdDr : Variables) -> (mWSJ : Registers lJ) ->
                                        Gen0 (fLLJk ** uMGOF ** Statement bcT bdDr mWSJ fLLJk uMGOF)

  sUnQiIB   : Statement_postV_postR_Gen
  lRQtHQD   : Statement_postV_postR_Gen
  ruJzDsgcS : Statement_postV_postR_Gen
  zbONvdwvg : Statement_postV_postR_Gen
  jUCrovX   : Statement_postV_postR_Gen
  uumdqi    : Statement_postV_postR_Gen
  rFJgeOC   : Statement_postV_postR_Gen
  iKwGywPrt : Statement_postV_postR_Gen
  vBZRvfhpm : Statement_postV_postR_Gen

  export
  wylUWaKXbMqAQ : Statement_postV_postR_Gen
  wylUWaKXbMqAQ Dry bdDr mWSJ = zEoyaqyKo
    [ (1  , sUnQiIB   Dry bdDr mWSJ)
    , (5  , lRQtHQD   Dry bdDr mWSJ)
    , (50 , ruJzDsgcS Dry bdDr mWSJ)
    , (50 , zbONvdwvg Dry bdDr mWSJ)
    , (10 , vBZRvfhpm Dry bdDr mWSJ)
    ]
  wylUWaKXbMqAQ (More b) bdDr mWSJ = zEoyaqyKo
    [ (1  , sUnQiIB   b bdDr mWSJ)
    , (5  , lRQtHQD   b bdDr mWSJ)
    , (50 , ruJzDsgcS b bdDr mWSJ)
    , (50 , zbONvdwvg b bdDr mWSJ)
    , (10 , jUCrovX   b bdDr mWSJ)
    , (10 , uumdqi    b bdDr mWSJ)
    , (200, rFJgeOC   b bdDr mWSJ)
    , (5  , iKwGywPrt b bdDr mWSJ)
    , (10 , vBZRvfhpm b bdDr mWSJ)
    ]

namespace Statements_given_preV_preR -- ncoUKrQtLrUXJJj

  sUnQiIB _ bdDr mWSJ = ilLg (_ ** _ ** nYH)

  lRQtHQD _ bdDr mWSJ = ilLg (_ ** _ ** !zqGrdsQpGnId. !zqGrdsQpGnId)

  ruJzDsgcS b bdDr mWSJ = do
    (h ** jG) <- stoOIkiYp bdDr
    ilLg (_ ** _ ** h #= !(kWoXjWs b))

  zbONvdwvg b bdDr mWSJ = ilLg (_ ** _ ** !zqGrdsQpGnId %= !(kWoXjWs b {t = !zqGrdsQpGnId}))

  jUCrovX b bdDr mWSJ = do
    (cdDWnLN ** hTfXlre ** zKhs) <- wylUWaKXbMqAQ b bdDr mWSJ
    --
    (cBNi ** _) <- fadNYKezKUZwrhVI b hTfXlre
    nwc         <- wylUWaKXbMqAQ b cdDWnLN hTfXlre cdDWnLN cBNi
    --
    (dbjSG ** _) <- fadNYKezKUZwrhVI b hTfXlre
    (_ ** yKWp)  <- wylUWaKXbMqAQ b cdDWnLN hTfXlre dbjSG
    --
    ilLg (_ ** _ ** iQA zKhs !(kWoXjWs b) nwc yKWp)

  uumdqi b bdDr mWSJ = do
    (_ ** _ ** fY) <- wylUWaKXbMqAQ b bdDr mWSJ
    (_ ** _ ** nW) <- wylUWaKXbMqAQ b bdDr mWSJ
    ilLg (_ ** _ ** pHSg !(kWoXjWs b) fY nW)

  rFJgeOC b bdDr mWSJ = do
    (isrz ** ieBZ ** y) <- wylUWaKXbMqAQ b bdDr mWSJ
    (_    ** _    ** a) <- wylUWaKXbMqAQ b isrz ieBZ
    ilLg (_ ** _ ** y >> a)

  iKwGywPrt b bdDr mWSJ = do
    (_ ** _ ** q) <- wylUWaKXbMqAQ b bdDr mWSJ
    ilLg (_ ** _ ** zFlux q)

  vBZRvfhpm b bdDr mWSJ = ilLg (_ ** _ ** dbUpQ !(kWoXjWs b {t=String'}))

namespace Statements_given_preV_preR_postV_postR -- ncoUKrQtLrUXJJj

  sUnQiIB _ bdDr mWSJ fLLJk uMGOF = case (qiEmI fLLJk bdDr, qiEmI uMGOF mWSJ) of
    (No _, _) => qnNdQ
    (_, No _) => qnNdQ
    (Yes Refl, Yes Refl) => ilLg nYH

  lRQtHQD _ bdDr mWSJ [] uMGOF = qnNdQ
  lRQtHQD _ bdDr mWSJ ((h, kM)::eARbBm) uMGOF = case (qiEmI eARbBm bdDr, qiEmI uMGOF mWSJ) of
    (No _, _) => qnNdQ
    (_, No _) => qnNdQ
    (Yes Refl, Yes Refl) => ilLg $ kM. h

  ruJzDsgcS b bdDr mWSJ fLLJk uMGOF = case (qiEmI fLLJk bdDr, qiEmI uMGOF mWSJ) of
    (No _, _) => qnNdQ
    (_, No _) => qnNdQ
    (Yes Refl, Yes Refl) => do
      (h ** jG) <- stoOIkiYp bdDr
      ilLg $ h #= !(kWoXjWs b)

  zbONvdwvg b bdDr mWSJ fLLJk (gT `With` (qlL, Just kM)) = case (qiEmI fLLJk bdDr, qiEmI gT mWSJ) of
    (Yes Refl, Yes Refl) => ilLg $ qlL %= !(kWoXjWs b)
    (No _, _)     => qnNdQ
    (_, No _)     => qnNdQ
  zbONvdwvg _ bdDr mWSJ fLLJk _ = qnNdQ

  jUCrovX b bdDr mWSJ fLLJk uMGOF = case qiEmI fLLJk bdDr of
    No _ => qnNdQ
    Yes Refl => do
      (cdDWnLN ** zKhs) <- wylUWaKXbMqAQ b bdDr mWSJ uMGOF
      --
      (cBNi ** _) <- fadNYKezKUZwrhVI b uMGOF
      nwc         <- wylUWaKXbMqAQ b cdDWnLN uMGOF cdDWnLN cBNi
      --
      (dbjSG ** _) <- fadNYKezKUZwrhVI b uMGOF
      (_ ** yKWp)  <- wylUWaKXbMqAQ b cdDWnLN uMGOF dbjSG
      --
      ilLg $ iQA zKhs !(kWoXjWs b) nwc yKWp

  uumdqi b bdDr mWSJ fLLJk (Merge oaF qoJ) = case qiEmI fLLJk bdDr of
    Yes Refl => do
      (_ ** fY) <- wylUWaKXbMqAQ b bdDr mWSJ oaF
      (_ ** nW) <- wylUWaKXbMqAQ b bdDr mWSJ qoJ
      ilLg $ pHSg !(kWoXjWs b) fY nW
    No _ => qnNdQ
  uumdqi b bdDr mWSJ fLLJk _ = qnNdQ

  rFJgeOC b bdDr mWSJ fLLJk uMGOF = do
    (isrz ** ieBZ ** zYHj) <- wylUWaKXbMqAQ b bdDr mWSJ
    dXpys                  <- wylUWaKXbMqAQ b isrz ieBZ fLLJk uMGOF
    ilLg $ zYHj >> dXpys

  iKwGywPrt b bdDr mWSJ fLLJk uMGOF = case qiEmI fLLJk bdDr of
    No _ => qnNdQ
    Yes Refl => do
      (_ ** iXXE) <- wylUWaKXbMqAQ b bdDr mWSJ uMGOF
      ilLg $ zFlux iXXE

  vBZRvfhpm b bdDr mWSJ fLLJk uMGOF = case (qiEmI fLLJk bdDr, qiEmI uMGOF mWSJ) of
    (No _, _) => qnNdQ
    (_, No _) => qnNdQ
    (Yes Refl, Yes Refl) => ilLg $ dbUpQ !(kWoXjWs b {t=String'})

namespace Statements_given_preV_preR_postR -- ncoUKrQtLrUXJJj

  sUnQiIB _ bdDr mWSJ uMGOF = case qiEmI uMGOF mWSJ of
    No _ => qnNdQ
    Yes Refl => ilLg (_ ** nYH)

  lRQtHQD _ bdDr mWSJ uMGOF = case qiEmI uMGOF mWSJ of
    No _ => qnNdQ
    Yes Refl => ilLg (_ ** !zqGrdsQpGnId. !zqGrdsQpGnId)

  ruJzDsgcS b bdDr mWSJ uMGOF = case qiEmI uMGOF mWSJ of
    No _ => qnNdQ
    Yes Refl => do
      (h ** jG) <- stoOIkiYp bdDr
      ilLg (_ ** h #= !(kWoXjWs b))

  zbONvdwvg b bdDr mWSJ (gT `With` (qlL, Just kM)) = case qiEmI gT mWSJ of
    Yes Refl => ilLg $ (_ ** qlL %= !(kWoXjWs b))
    No _ => qnNdQ
  zbONvdwvg _ bdDr mWSJ _ = qnNdQ

  jUCrovX b bdDr mWSJ uMGOF = do
    (cdDWnLN ** zKhs) <- wylUWaKXbMqAQ b bdDr mWSJ uMGOF
    --
    (cBNi ** _) <- fadNYKezKUZwrhVI b uMGOF
    nwc         <- wylUWaKXbMqAQ b cdDWnLN uMGOF cdDWnLN cBNi
    --
    (dbjSG ** _) <- fadNYKezKUZwrhVI b uMGOF
    (_ ** yKWp)  <- wylUWaKXbMqAQ b cdDWnLN uMGOF dbjSG
    --
    ilLg (_ ** iQA zKhs !(kWoXjWs b) nwc yKWp)

  uumdqi b bdDr mWSJ (Merge oaF qoJ) = do
      (_ ** fY) <- wylUWaKXbMqAQ b bdDr mWSJ oaF
      (_ ** nW) <- wylUWaKXbMqAQ b bdDr mWSJ qoJ
      ilLg (_ ** pHSg !(kWoXjWs b) fY nW)
  uumdqi b bdDr mWSJ _ = qnNdQ

  rFJgeOC b bdDr mWSJ uMGOF = do
    (isrz ** ieBZ ** zYHj) <- wylUWaKXbMqAQ b bdDr mWSJ
    (_           ** dXpys) <- wylUWaKXbMqAQ b isrz ieBZ uMGOF
    ilLg $ (_ ** zYHj >> dXpys)

  iKwGywPrt b bdDr mWSJ uMGOF = do
    (_ ** iXXE) <- wylUWaKXbMqAQ b bdDr mWSJ uMGOF
    ilLg $ (_ ** zFlux iXXE)

  vBZRvfhpm b bdDr mWSJ uMGOF = case qiEmI uMGOF mWSJ of
    No _ => qnNdQ
    Yes Refl => ilLg $ (_ ** dbUpQ !(kWoXjWs b {t=String'}))
