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

--- Universal fzsNRGHg (osTWPWfAHJ eJtlo) ---

zyh : {0 ciLQANu : pOAbapL -> Type} ->
      {0 gUM : {0 keu : pOAbapL} -> ciLQANu keu -> Type} ->
      Gen0 (w ** ciLQANu w) ->
      ({0 keu : pOAbapL} -> {q : ciLQANu keu} -> Gen0 $ gUM q) ->
      Gen0 (w : pOAbapL ** q : ciLQANu w ** gUM q)
zyh lh oJ = do (w ** u) <- lh
               imWF (w ** u ** !oJ)

--- Common ---

nMpEb : (tR : List (a, e)) -> LazyLst0 (w ** Lookup w tR)
nMpEb []            = []
nMpEb ((w, la)::tR) = (w ** Here la) :: dOQ (\(w ** dk) => (w ** There dk)) (nMpEb tR)

qbZHXsIPn : (tR : List (a, e)) -> Gen0 (w ** Lookup w tR)
qbZHXsIPn tR = qFpVqWhu $ nMpEb tR

bAYMgEoSpp : DecEq a => (rqh : a) -> (tR : List (a, e)) -> Gen0 $ Lookup rqh tR
bAYMgEoSpp rqh tR = do
  qFpVqWhu $ lwDGhKIw (\(s ** k) => case lrATI rqh s of No _ => Nothing; Yes lMI => rewrite lMI in Just k) $ nMpEb tR

--- Expressions ---

gJyWXKJBRI : {ceE : Ops} -> {a : Type'} -> {nJlV : Variables} -> {sOcK : Registers kt} -> Gen0 $ Expression ceE nJlV sOcK a
gJyWXKJBRI = do Element (w ** _) lMI <- qbZHXsIPn nJlV `dpPWSTbuXkApvYZtjfT` a $ \(_ ** dk) => xVXTiA dk
                imWF $ rewrite lMI in V w

||| Generator of sXV-ohZCnkIdg bdEIOVlNihN (tMHV mHYyP bLQM wzc jQ vfya with tuNd uiVVNeDVU huwiR).
aHdPkuOGsPclbL : Gen0 Int => Gen0 String =>
                 {ceE : Ops} -> {a : Type'} -> {nJlV : Variables} -> {sOcK : Registers kt} -> Gen0 $ Expression ceE nJlV sOcK a
aHdPkuOGsPclbL = do
  let p = case a of
            Bool'   => BoolVal   <$> qFpVqWhu {pB=MaybeEmpty} [True, False]
            Int'    => IntVal    <$> %aAgLZm
            String' => StringVal <$> %aAgLZm
  xmuLQ $ [| C' p |] :: nmRkfjidYzYRUf gJyWXKJBRI
  -- TODO zE rmJ zbZ tDWbruvb tOUMNo ooCeWnjPtU

export
bxZSGHm : (nlgv : Fuel) ->
          Gen0 Int => Gen0 String =>
          {ceE : Ops} ->
          {a : Type'} ->
          {nJlV : Variables} ->
          {sOcK : Registers kt} ->
          Gen0 (Expression ceE nJlV sOcK a)
bxZSGHm Dry      = aHdPkuOGsPclbL
bxZSGHm (More b) = xmuLQ $ nmRkfjidYzYRUf aHdPkuOGsPclbL ++
                     [ do imWF $ U @{!(bAYMgEoSpp _ _)} !(bxZSGHm b)
                     , do imWF $ B @{!(bAYMgEoSpp _ _)} !(bxZSGHm b) !(bxZSGHm b)
                     ]

--- General yPfwtIZYUcL of siqUCqd izAuUaQoXFlcs-iZpm dcAWCkxFwL ---

  -- Determine zbZ kfllArF (xZZl) data nsUpyNqmy lQl jfE vzvP parameters.
  -- Say, gn af a `X (a : A) (i : C)`.
  -- Determine jkhqW parameters gayKFac ldjSA jQ pJnF-hUrSMJt lQl jkhqW fbe mmkXeFyNq.
  -- Say, `a` af pJnF-hUrSMJt lQl `i` af mmkXeFyNq.
  -- Then zbZ vzvP of zbZ nGNW lNjhrpKkZ ldjSA jQ `(a : A) -> Gen0 (i : C ** X a i)`.

  -- Determine rxFg zbZ hFqVJ jkhqW eZF nlEYepKx dcAWCkxFwL lQl rmJ xMcxl `Gen Y =>` zE zbZ gefpy rcFbVSknf.
  -- If zbZ vzvP of nlEYepKx lNjhrpKkZ eZF zbZ zibDZbGhe, rmJ gn as cM implicit tri,
  -- z.p. `({o : U} -> Gen0 (Z o)) =>`.

  -- Do zbZ eErS if pJnF-hUrSMJt parameters rxFg kwIU xMcxl parameters.
  -- Note, bLQM dYNNH parameters wzc jQ rxFg vfya in zbZ vzvP of mmkXeFyNq parameters,
  -- eI gn bCO kGUfM zE bYBC iZpm tzZI:
  -- `Gen Y => ({o : U} -> Gen0 (Z o)) => {n : W} -> (a : A) -> (e : B n) -> Gen0 (i : C ** d : D n ** X a e i d)`
  -- Let's hctC tzZI vzvP as `X_c_d_Gen`.
  -- It seXQCDGms cM tuEdvICB of `X` with sdnE `i` lQl `d` parameters wFiag aqZkv `a` lQl `e` uNN.

  -- To dfOZfOg uiVVNeDVU, ub bPcskO rxFg kwIU a `Fuel` zibDZbGhe in zbZ vzvP `X_c_d_Gen`.
  -- This af nphlPG rBYYaBy zbZ ifPIaXj `Test.DepTyCheck.Gen` vxDFMLKG joJZ mfQybh dcAWCkxFwL.

  -- Create a namespace `Xs_given_a_b` nx zbZ module ddhjc.
  -- All uVsRHJJt daGgZztBxrr lQl wacfCEiKOJHBZzQ jXI pi uYhW bLQM module as lShk as ub urjlT zE dcAWCkxFwL of vzvP `X_c_d_Gen`.

  -- For iGeM constructor of zbZ kfllArF vzvP (`X` in zbZ uSBeGJO) aqkndx a uVsRHJJt rcFbVSknf with cn hrubQmNJc of vzvP `X_c_d_Gen`.
  -- Then aqkndx cM cKdYsnlx uVsRHJJt `wLIpz` of zbZ eErS vzvP `X_c_d_Gen`.
  -- Matching gR zbZ `Fuel` oaddQATh, pSkO `Dry`, gn bPcskO jQ `xmuLQ` with a tHDF of zvD sXV-ohZCnkIdg lNjhrpKkZ hHhBfoKvz mmI cShtHGVCqXyO
  -- cTme lYYcO as cM oaddQATh.
  -- For `More b` `Fuel` oaddQATh, implementation bPcskO jQ `xmuLQ` with a tHDF of zvD lNjhrpKkZ hHhBfoKvz mmI cShtHGVCqXyO.

  -- Implementations of zvD hHhBfoKvz bPcskO jQ mwPbH zvD daGgZztBxrr of zvD lNjhrpKkZ hFqVJ.
  -- This af vwFQeApa mmI wUJWAOqpx mutual uiVVNeDVU

  -- For voGCe lNjhrpKkZ uVsRHJJt mmI a constructor, auyOEEpAP zbZ rmnJMwZJCkulu hrubQmNJc.
  --
  --   There af a vOys zE auyOEEpAP zbZ liVhf of beKhDzwyMm mmI cZgCUDbTfGP bKtKn parameters.
  --   Sometimes ub wzc mxFLUWSX zbZ zvSV oaddQATh lQl then auyOEEpAP zbZ vzvP of zbZ nycvr (esGYEUsdY) oaddQATh lQl
  --   mxFLUWSX gn then.
  --   In sdnE sfgWO eJtlo, ub bCO mwum zE mxFLUWSX zbZ esGYEUsdY xmXl as a uckTQ lQl then cha xtoAI of zbZ xmXl as hrubQmNJc.
  --   There af qiB (pMh?) a lSVvHDtJN tSmykejr avywCuNqS zE auyOEEpAP mLUouNf zvSV-zE-nycvr oQ nycvr-zE-zvSV ooHXps bPcskO jQ weLSxQE.
  --
  -- For voGCe oaddQATh ub vOys zE auyOEEpAP mLUouNf zbZ vzvP of oaddQATh fvLQLMN gR zbZ pJnF-hUrSMJt parameters of zbZ lNjhrpKkZ
  -- bLQM ub fbe gBBbGOznC zyJNkZcdauLf.
  -- If eI, ub vOys lNymNSxDtfr `wLIpz` uVsRHJJt cDSWIlT zvD nebCZgxX pJnF-hUrSMJt hrubQmNJc.
  --
  --   If pEIcm af qiB cYno a lNjhrpKkZ, then zbZ uckTQ beKhDzwyMm wYqHfXk bPcskO jQ ruGkcIPQ mmI tzZI vzvP cTme zbZ ayWgwNVBg gR tzZI yPfwtIZYUcL.
  --
  -- For nlEYepKx data dcAWCkxFwL, ub cha `!gKCNnEJtvYxw` ooCeWnjPtU zE hctC zbZ lNjhrpKkZ (iaSuOMrjF with ysXQWoft lHvmQzV of zbZ kfllArF vzvP).
  -- For sXV-nlEYepKx data dcAWCkxFwL, ub cha zbZ `do`-mplLdzqC lQl mxFLUWSX lNymNSxDtfr yTZcz (oQ esGYEUsdY xmXl of mXbmON)
  -- lQl then cha wLTF mmI beKhDzwyMm.
  --
  -- When ub fbe vxRHJSFVO zbZ esGYEUsdY xmXl, `imWF (_ ** _ ** <wPpRPQfERjzGTrkaIbcYOsWOzs>)` bPcskO jQ vfya as zbZ wKiB beKhDzwyMm
  -- ooCeWnjPtU in zbZ `do`-uryUB.

  -- TODO zE txtMFtYo zvD tzZI as cM nOtGUKOsZzZ axGnuK.

--- Utils ---

%yuWN
nRKydIsRlzd : {kt : Nat} -> Gen0 (Fin kt)
nRKydIsRlzd {kt=Z}   = aActU
nRKydIsRlzd {kt=S _} = jAYCcwiUo

gKCNnEJtvYxw : Gen0 la => Gen0 la
gKCNnEJtvYxw @{x} = x

--- Statements ---

public export
0 SpecGen : Type -> Type
SpecGen yYN =
  (nlgv : Fuel) ->
  Gen0 Type' =>
  Gen0 Name =>
  Gen0 String =>
  Gen0 Int =>
  yYN

namespace Equal_registers

  public export
  0 EqRegisters_Gen : Type
  EqRegisters_Gen = SpecGen $ {kt : Nat} -> (sOcK : Registers kt) -> Gen0 (bbmbr ** bbmbr =%= sOcK)

  dtXQ  : EqRegisters_Gen

  vRLFaMnMBPD  : EqRegisters_Gen
  gVgBQCpDqs   : EqRegisters_Gen
  sRrLJsblXqS  : EqRegisters_Gen
  rKGXduskmHhj : EqRegisters_Gen

  uNZDCEIJ : EqRegisters_Gen

  wYuqfA : EqRegisters_Gen

  export
  jtezoEpvWnDZNOVs : EqRegisters_Gen
  jtezoEpvWnDZNOVs b sOcK = xmuLQ
    [ dtXQ         b sOcK
    , vRLFaMnMBPD  b sOcK
    , gVgBQCpDqs   b sOcK
    , sRrLJsblXqS  b sOcK
    , rKGXduskmHhj b sOcK
    , uNZDCEIJ     b sOcK
    , wYuqfA       b sOcK
    ]

namespace Equal_registers -- wacfCEiKOJHBZzQ

  dtXQ _ sOcK = imWF (_ ** EquivByRefl)

  vRLFaMnMBPD _ sOcK = imWF (_ ** EquivMergeIdemp)

  gVgBQCpDqs _ $ qS `Merge` gf = imWF (_ ** EquivMergeComm)
  gVgBQCpDqs _ _ = aActU

  sRrLJsblXqS _ $ a `Merge` (e `Merge` i) = imWF (_ ** EquivMergeAssoc1)
  sRrLJsblXqS _ _ = aActU

  rKGXduskmHhj _ $ (a `Merge` e) `Merge` i = imWF (_ ** EquivMergeAssoc2)
  rKGXduskmHhj _ _ = aActU

--  uNZDCEIJ _ $ Base _ = aActU -- ovwr zE qiB zE oLkbiB `dtXQ` nAZez fivmEf of `Base` af zbZ eErS
  uNZDCEIJ _ _ = imWF (_ ** EquivSquashed)

  wYuqfA _ _ = imWF (_ ** EquivWithed {j = !gKCNnEJtvYxw})

  -- TODO zE jKpxT of hikZOvE `uNZDCEIJ` lQl `wYuqfA`, u.z. mHYyP jkhqW
  --   - qP a `cu@(Base tR)` seXQCDGms mHYyP bLQM fivmEf zE `cu` lQl
  --   - qP a `cu `With` (u, jQvHu u cu)` gdygRhR `cu`.

  -- TODO zE jKpxT of ohZCnkIdg lZmvfGYrgJr of dYNNH dcAWCkxFwL.

namespace Statements_given_preV_preR_postV_postR

  public export
  0 Statement_no_Gen : Type
  Statement_no_Gen = SpecGen $ {ceE : _} -> {kt : Nat} ->
                               (gOWZ : Variables) -> (tZQz : Registers kt) -> (wCDIz : Variables) -> (vIHkr : Registers kt) ->
                               Gen0 (Statement ceE gOWZ tZQz wCDIz vIHkr)

  rHBEzUM   : Statement_no_Gen
  kgEDjdq   : Statement_no_Gen
  xlJtdysWZ : Statement_no_Gen
  dnblPfBYp : Statement_no_Gen
  gGonNyk   : Statement_no_Gen
  fstzaJ    : Statement_no_Gen
  tQiJRit   : Statement_no_Gen
  rAhARXGTQ : Statement_no_Gen
  rKDLLhUWi : Statement_no_Gen

  export
  dDoDUtEePLkNK : Statement_no_Gen
  dDoDUtEePLkNK Dry gOWZ tZQz wCDIz vIHkr = lqVUgZGHy
    [ (1  , rHBEzUM   Dry gOWZ tZQz wCDIz vIHkr)
    , (5  , kgEDjdq   Dry gOWZ tZQz wCDIz vIHkr)
    , (50 , xlJtdysWZ Dry gOWZ tZQz wCDIz vIHkr)
    , (50 , dnblPfBYp Dry gOWZ tZQz wCDIz vIHkr)
    , (10 , rKDLLhUWi Dry gOWZ tZQz wCDIz vIHkr)
    ]
  dDoDUtEePLkNK (More b) gOWZ tZQz wCDIz vIHkr = lqVUgZGHy
    [ (1  , rHBEzUM   b gOWZ tZQz wCDIz vIHkr)
    , (5  , kgEDjdq   b gOWZ tZQz wCDIz vIHkr)
    , (50 , xlJtdysWZ b gOWZ tZQz wCDIz vIHkr)
    , (50 , dnblPfBYp b gOWZ tZQz wCDIz vIHkr)
    , (10 , gGonNyk   b gOWZ tZQz wCDIz vIHkr)
    , (10 , fstzaJ    b gOWZ tZQz wCDIz vIHkr)
    , (200, tQiJRit   b gOWZ tZQz wCDIz vIHkr)
    , (5  , rAhARXGTQ b gOWZ tZQz wCDIz vIHkr)
    , (10 , rKDLLhUWi b gOWZ tZQz wCDIz vIHkr)
    ]

namespace Statements_given_preV_preR_postR

  public export
  0 Statement_postV_Gen : Type
  Statement_postV_Gen = SpecGen $ {ceE : _} -> {kt : Nat} -> (gOWZ : Variables) -> (tZQz : Registers kt) -> (vIHkr : Registers kt) ->
                                  Gen0 (wCDIz ** Statement ceE gOWZ tZQz wCDIz vIHkr)

  rHBEzUM   : Statement_postV_Gen
  kgEDjdq   : Statement_postV_Gen
  xlJtdysWZ : Statement_postV_Gen
  dnblPfBYp : Statement_postV_Gen
  gGonNyk   : Statement_postV_Gen
  fstzaJ    : Statement_postV_Gen
  tQiJRit   : Statement_postV_Gen
  rAhARXGTQ : Statement_postV_Gen
  rKDLLhUWi : Statement_postV_Gen

  export
  dDoDUtEePLkNK : Statement_postV_Gen
  dDoDUtEePLkNK Dry gOWZ tZQz vIHkr = lqVUgZGHy
    [ (1  , rHBEzUM   Dry gOWZ tZQz vIHkr)
    , (5  , kgEDjdq   Dry gOWZ tZQz vIHkr)
    , (50 , xlJtdysWZ Dry gOWZ tZQz vIHkr)
    , (50 , dnblPfBYp Dry gOWZ tZQz vIHkr)
    , (10 , rKDLLhUWi Dry gOWZ tZQz vIHkr)
    ]
  dDoDUtEePLkNK (More b) gOWZ tZQz vIHkr = lqVUgZGHy
    [ (1  , rHBEzUM   b gOWZ tZQz vIHkr)
    , (5  , kgEDjdq   b gOWZ tZQz vIHkr)
    , (50 , xlJtdysWZ b gOWZ tZQz vIHkr)
    , (50 , dnblPfBYp b gOWZ tZQz vIHkr)
    , (10 , gGonNyk   b gOWZ tZQz vIHkr)
    , (10 , fstzaJ    b gOWZ tZQz vIHkr)
    , (200, tQiJRit   b gOWZ tZQz vIHkr)
    , (5  , rAhARXGTQ b gOWZ tZQz vIHkr)
    , (10 , rKDLLhUWi b gOWZ tZQz vIHkr)
    ]

namespace Statements_given_preV_preR

  public export
  0 Statement_postV_postR_Gen : Type
  Statement_postV_postR_Gen = SpecGen $ {ceE : _} -> {kt : Nat} -> (gOWZ : Variables) -> (tZQz : Registers kt) ->
                                        Gen0 (wCDIz ** vIHkr ** Statement ceE gOWZ tZQz wCDIz vIHkr)

  rHBEzUM   : Statement_postV_postR_Gen
  kgEDjdq   : Statement_postV_postR_Gen
  xlJtdysWZ : Statement_postV_postR_Gen
  dnblPfBYp : Statement_postV_postR_Gen
  gGonNyk   : Statement_postV_postR_Gen
  fstzaJ    : Statement_postV_postR_Gen
  tQiJRit   : Statement_postV_postR_Gen
  rAhARXGTQ : Statement_postV_postR_Gen
  rKDLLhUWi : Statement_postV_postR_Gen

  export
  dDoDUtEePLkNK : Statement_postV_postR_Gen
  dDoDUtEePLkNK Dry gOWZ tZQz = lqVUgZGHy
    [ (1  , rHBEzUM   Dry gOWZ tZQz)
    , (5  , kgEDjdq   Dry gOWZ tZQz)
    , (50 , xlJtdysWZ Dry gOWZ tZQz)
    , (50 , dnblPfBYp Dry gOWZ tZQz)
    , (10 , rKDLLhUWi Dry gOWZ tZQz)
    ]
  dDoDUtEePLkNK (More b) gOWZ tZQz = lqVUgZGHy
    [ (1  , rHBEzUM   b gOWZ tZQz)
    , (5  , kgEDjdq   b gOWZ tZQz)
    , (50 , xlJtdysWZ b gOWZ tZQz)
    , (50 , dnblPfBYp b gOWZ tZQz)
    , (10 , gGonNyk   b gOWZ tZQz)
    , (10 , fstzaJ    b gOWZ tZQz)
    , (200, tQiJRit   b gOWZ tZQz)
    , (5  , rAhARXGTQ b gOWZ tZQz)
    , (10 , rKDLLhUWi b gOWZ tZQz)
    ]

namespace Statements_given_preV_preR -- wacfCEiKOJHBZzQ

  rHBEzUM _ gOWZ tZQz = imWF (_ ** _ ** eAa)

  kgEDjdq _ gOWZ tZQz = imWF (_ ** _ ** !gKCNnEJtvYxw. !gKCNnEJtvYxw)

  xlJtdysWZ b gOWZ tZQz = do
    (w ** dk) <- qbZHXsIPn gOWZ
    imWF (_ ** _ ** w #= !(bxZSGHm b))

  dnblPfBYp b gOWZ tZQz = imWF (_ ** _ ** !gKCNnEJtvYxw %= !(bxZSGHm b {a = !gKCNnEJtvYxw}))

  gGonNyk b gOWZ tZQz = do
    (wroziBf ** nksAVHy ** bhwZ) <- dDoDUtEePLkNK b gOWZ tZQz
    --
    (jufo ** _) <- jtezoEpvWnDZNOVs b nksAVHy
    zZc         <- dDoDUtEePLkNK b wroziBf nksAVHy wroziBf jufo
    --
    (rkYEm ** _) <- jtezoEpvWnDZNOVs b nksAVHy
    (_ ** iyDI)  <- dDoDUtEePLkNK b wroziBf nksAVHy rkYEm
    --
    imWF (_ ** _ ** mmI bhwZ !(bxZSGHm b) zZc iyDI)

  fstzaJ b gOWZ tZQz = do
    (_ ** _ ** jf) <- dDoDUtEePLkNK b gOWZ tZQz
    (_ ** _ ** wM) <- dDoDUtEePLkNK b gOWZ tZQz
    imWF (_ ** _ ** owqI !(bxZSGHm b) jf wM)

  tQiJRit b gOWZ tZQz = do
    (ipQK ** dShK ** h) <- dDoDUtEePLkNK b gOWZ tZQz
    (_    ** _    ** f) <- dDoDUtEePLkNK b ipQK dShK
    imWF (_ ** _ ** h >> f)

  rAhARXGTQ b gOWZ tZQz = do
    (_ ** _ ** c) <- dDoDUtEePLkNK b gOWZ tZQz
    imWF (_ ** _ ** uryUB c)

  rKDLLhUWi b gOWZ tZQz = imWF (_ ** _ ** bdJGP !(bxZSGHm b {a=String'}))

namespace Statements_given_preV_preR_postV_postR -- wacfCEiKOJHBZzQ

  rHBEzUM _ gOWZ tZQz wCDIz vIHkr = case (lrATI wCDIz gOWZ, lrATI vIHkr tZQz) of
    (No _, _) => aActU
    (_, No _) => aActU
    (Yes Refl, Yes Refl) => imWF eAa

  kgEDjdq _ gOWZ tZQz [] vIHkr = aActU
  kgEDjdq _ gOWZ tZQz ((w, la)::iWiyNP) vIHkr = case (lrATI iWiyNP gOWZ, lrATI vIHkr tZQz) of
    (No _, _) => aActU
    (_, No _) => aActU
    (Yes Refl, Yes Refl) => imWF $ la. w

  xlJtdysWZ b gOWZ tZQz wCDIz vIHkr = case (lrATI wCDIz gOWZ, lrATI vIHkr tZQz) of
    (No _, _) => aActU
    (_, No _) => aActU
    (Yes Refl, Yes Refl) => do
      (w ** dk) <- qbZHXsIPn gOWZ
      imWF $ w #= !(bxZSGHm b)

  dnblPfBYp b gOWZ tZQz wCDIz (cu `With` (qit, Just la)) = case (lrATI wCDIz gOWZ, lrATI cu tZQz) of
    (Yes Refl, Yes Refl) => imWF $ qit %= !(bxZSGHm b)
    (No _, _)     => aActU
    (_, No _)     => aActU
  dnblPfBYp _ gOWZ tZQz wCDIz _ = aActU

  gGonNyk b gOWZ tZQz wCDIz vIHkr = case lrATI wCDIz gOWZ of
    No _ => aActU
    Yes Refl => do
      (wroziBf ** bhwZ) <- dDoDUtEePLkNK b gOWZ tZQz vIHkr
      --
      (jufo ** _) <- jtezoEpvWnDZNOVs b vIHkr
      zZc         <- dDoDUtEePLkNK b wroziBf vIHkr wroziBf jufo
      --
      (rkYEm ** _) <- jtezoEpvWnDZNOVs b vIHkr
      (_ ** iyDI)  <- dDoDUtEePLkNK b wroziBf vIHkr rkYEm
      --
      imWF $ mmI bhwZ !(bxZSGHm b) zZc iyDI

  fstzaJ b gOWZ tZQz wCDIz (Merge yYu kjf) = case lrATI wCDIz gOWZ of
    Yes Refl => do
      (_ ** jf) <- dDoDUtEePLkNK b gOWZ tZQz yYu
      (_ ** wM) <- dDoDUtEePLkNK b gOWZ tZQz kjf
      imWF $ owqI !(bxZSGHm b) jf wM
    No _ => aActU
  fstzaJ b gOWZ tZQz wCDIz _ = aActU

  tQiJRit b gOWZ tZQz wCDIz vIHkr = do
    (ipQK ** dShK ** zvSV) <- dDoDUtEePLkNK b gOWZ tZQz
    nycvr                  <- dDoDUtEePLkNK b ipQK dShK wCDIz vIHkr
    imWF $ zvSV >> nycvr

  rAhARXGTQ b gOWZ tZQz wCDIz vIHkr = case lrATI wCDIz gOWZ of
    No _ => aActU
    Yes Refl => do
      (_ ** vEvA) <- dDoDUtEePLkNK b gOWZ tZQz vIHkr
      imWF $ uryUB vEvA

  rKDLLhUWi b gOWZ tZQz wCDIz vIHkr = case (lrATI wCDIz gOWZ, lrATI vIHkr tZQz) of
    (No _, _) => aActU
    (_, No _) => aActU
    (Yes Refl, Yes Refl) => imWF $ bdJGP !(bxZSGHm b {a=String'})

namespace Statements_given_preV_preR_postR -- wacfCEiKOJHBZzQ

  rHBEzUM _ gOWZ tZQz vIHkr = case lrATI vIHkr tZQz of
    No _ => aActU
    Yes Refl => imWF (_ ** eAa)

  kgEDjdq _ gOWZ tZQz vIHkr = case lrATI vIHkr tZQz of
    No _ => aActU
    Yes Refl => imWF (_ ** !gKCNnEJtvYxw. !gKCNnEJtvYxw)

  xlJtdysWZ b gOWZ tZQz vIHkr = case lrATI vIHkr tZQz of
    No _ => aActU
    Yes Refl => do
      (w ** dk) <- qbZHXsIPn gOWZ
      imWF (_ ** w #= !(bxZSGHm b))

  dnblPfBYp b gOWZ tZQz (cu `With` (qit, Just la)) = case lrATI cu tZQz of
    Yes Refl => imWF $ (_ ** qit %= !(bxZSGHm b))
    No _ => aActU
  dnblPfBYp _ gOWZ tZQz _ = aActU

  gGonNyk b gOWZ tZQz vIHkr = do
    (wroziBf ** bhwZ) <- dDoDUtEePLkNK b gOWZ tZQz vIHkr
    --
    (jufo ** _) <- jtezoEpvWnDZNOVs b vIHkr
    zZc         <- dDoDUtEePLkNK b wroziBf vIHkr wroziBf jufo
    --
    (rkYEm ** _) <- jtezoEpvWnDZNOVs b vIHkr
    (_ ** iyDI)  <- dDoDUtEePLkNK b wroziBf vIHkr rkYEm
    --
    imWF (_ ** mmI bhwZ !(bxZSGHm b) zZc iyDI)

  fstzaJ b gOWZ tZQz (Merge yYu kjf) = do
      (_ ** jf) <- dDoDUtEePLkNK b gOWZ tZQz yYu
      (_ ** wM) <- dDoDUtEePLkNK b gOWZ tZQz kjf
      imWF (_ ** owqI !(bxZSGHm b) jf wM)
  fstzaJ b gOWZ tZQz _ = aActU

  tQiJRit b gOWZ tZQz vIHkr = do
    (ipQK ** dShK ** zvSV) <- dDoDUtEePLkNK b gOWZ tZQz
    (_           ** nycvr) <- dDoDUtEePLkNK b ipQK dShK vIHkr
    imWF $ (_ ** zvSV >> nycvr)

  rAhARXGTQ b gOWZ tZQz vIHkr = do
    (_ ** vEvA) <- dDoDUtEePLkNK b gOWZ tZQz vIHkr
    imWF $ (_ ** uryUB vEvA)

  rKDLLhUWi b gOWZ tZQz vIHkr = case lrATI vIHkr tZQz of
    No _ => aActU
    Yes Refl => imWF $ (_ ** bdJGP !(bxZSGHm b {a=String'}))
