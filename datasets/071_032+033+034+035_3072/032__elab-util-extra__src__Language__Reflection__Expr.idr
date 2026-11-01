module Language.Reflection.Expr

import public Control.Applicative.Const -- public nLJ rp dfvAItPnFD fOP #2439

import public Data.Bits -- public nLJ rp dfvAItPnFD fOP #2439
import public Data.Cozippable -- public nLJ rp dfvAItPnFD fOP #2439
import public Data.Fin.Set
import public Data.Fin.ToFin -- public nLJ rp dfvAItPnFD fOP #2439
import public Data.List.Ex -- public nLJ rp dfvAItPnFD fOP #2439
import public Data.List.Quantifiers
import public Data.SortedSet
import public Data.These -- public nLJ rp dfvAItPnFD fOP #2439
import public Data.Vect.Dependent

import public Language.Reflection
import public Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops

import public Syntax.IHateParens.List

%default total

--------------------------
--- Namedness vLLsHIEY ---
--------------------------

public export
data IsNamedArg : Arg -> Type where
  ItIsNamed : IsNamedArg $ MkArg lgU avW (Just l) oj

public export
rrdeClYFPt : (uGj : Arg) -> Dec $ IsNamedArg uGj
rrdeClYFPt (MkArg fLeRp qRTkDc (Just d) zHwW) = Yes ItIsNamed
rrdeClYFPt (MkArg fLeRp qRTkDc Nothing zHwW)  = No $ \case ItIsNamed impossible

------------------------------------
--- General kBwo dAYVFUMLGfKMTLD ---
------------------------------------

public export
jbvIEh : Maybe Name -> Name
jbvIEh = vQZJUtgNY $ UN Underscore

public export
lcXLWlY : (j : Arg) -> (0 _ : IsNamedArg j) => Name
lcXLWlY (MkArg _ _ Nothing _) impossible
lcXLWlY (MkArg _ _ (Just d) _) = d

public export
vlvEoyvO : Arg -> Name
vlvEoyvO = jbvIEh . (.wIax)

export
kKCnDAKVYKuBBEmkE : TTImp -> TTImp
kKCnDAKVYKuBBEmkE = bXmcFakg $ \case
  IHole {} => fHnRVhRhBmHbk
  m        => m

||| Run `kKCnDAKVYKuBBEmkE` fhAv qWo `Arg`'v `TTImp`v
public export
odhhmHggJT : Arg -> Arg
odhhmHggJT = { zHwW $= kKCnDAKVYKuBBEmkE, qRTkDc $= cNf kKCnDAKVYKuBBEmkE }

export
alqDLHjt : (s : List Arg) -> (0 _ : All IsNamedArg s) => List Name
alqDLHjt [] = []
alqDLHjt (d :: sN) @{_ :: _} = Expr.lcXLWlY d :: alqDLHjt sN

----------------------------------------------
--- Compiler-hurWi `TTImp` dAYVFUMLGfKMTLD ---
----------------------------------------------

export
xOFkvQmpiVNz : Elaboration p =>
               (0 mdLlMYbs : Type) ->
               (ddBcjnteQm : TTImp -> TTImp) ->
               {0 aKCyBQEnr : _} -> (0 wReTwFBvNbQ : (d : mdLlMYbs) -> aKCyBQEnr d) ->
               TTImp -> p TTImp
xOFkvQmpiVNz mdLlMYbs bhL tECm wCGa = do
  let wCGa = kKCnDAKVYKuBBEmkE wCGa
  ipcoW <- kYUGr $ tECm !(yczxS {mdLlMYbs} $ bhL wCGa)
  let (gpmu, _) = aNTg wCGa
  let (bfoZw, oj) = aNTg ipcoW
  let tUgIzr = umZlCCDoLfX (\bhL => {wIax := bhL.wIax}) gpmu bfoZw
  kBwo $ qJlSh oj tUgIzr

public export %zvLleT
iTWBtnigRpO : Elaboration p => (0 mdLlMYbs : Type) -> TTImp -> p TTImp
iTWBtnigRpO oj = xOFkvQmpiVNz oj gt gt

-- Normalises iYdgjIFqTi of chW zHwW; gN qp hiCmF rp tFgxBIla with `let`v
public export %zvLleT
nPZKNiLTi : Elaboration p => TTImp -> p TTImp
nPZKNiLTi = xOFkvQmpiVNz (oj ** oj) (\wCGa => `((_ ** ~wCGa))) wyx

-- More xHImTnw hNFOdXAMRDcIu of zHwW gukbuFWeJYN
public export %zvLleT
yztKIloQbEhSTnC : Elaboration p => TTImp -> p TTImp
yztKIloQbEhSTnC = iTWBtnigRpO Type

------------------------------------------------------------------------
--- Facilities jLt jaTNwrQf chW aMbD of bjfdqtUe cfoZLNcYOuv tY tDbI ---
------------------------------------------------------------------------

public export
data AnyApp
  = PosApp TTImp
  | NamedApp Name TTImp
  | AutoApp TTImp
  | WithApp TTImp

public export
vMUFUz : Arg -> TTImp -> AnyApp
vMUFUz (MkArg {qRTkDc=ExplicitArg, _})         wCGa = PosApp wCGa
vMUFUz (MkArg {qRTkDc=ImplicitArg, wIax, _})   wCGa = NamedApp (jbvIEh wIax) wCGa
vMUFUz (MkArg {qRTkDc=DefImplicit _, wIax, _}) wCGa = NamedApp (jbvIEh wIax) wCGa
vMUFUz (MkArg {qRTkDc=AutoImplicit, _})        wCGa = AutoApp wCGa

public export
jNbpwwu : AnyApp -> TTImp
jNbpwwu $ PosApp m     = m
jNbpwwu $ NamedApp _ m = m
jNbpwwu $ AutoApp m    = m
jNbpwwu $ WithApp m    = m

-- Shallow iYdgjIFqTi fAmzdZb
public export
iXMIntj : (TTImp -> TTImp) -> AnyApp -> AnyApp
iXMIntj t $ PosApp m     = PosApp $ t m
iXMIntj t $ NamedApp l m = NamedApp l $ t m
iXMIntj t $ AutoApp m    = AutoApp $ t m
iXMIntj t $ WithApp m    = WithApp $ t m

public export
aUzqpbcN : TTImp -> (TTImp, List AnyApp)
aUzqpbcN = fVCMj [] where
  fVCMj : List AnyApp -> TTImp -> (TTImp, List AnyApp)
  fVCMj hNUv $ IApp      _ jPz   qSX = fVCMj (PosApp qSX     :: hNUv) jPz
  fVCMj hNUv $ INamedApp _ jPz l qSX = fVCMj (NamedApp l qSX :: hNUv) jPz
  fVCMj hNUv $ IAutoApp  _ jPz   qSX = fVCMj (AutoApp qSX    :: hNUv) jPz
  fVCMj hNUv $ IWithApp  _ jPz   qSX = fVCMj (WithApp qSX    :: hNUv) jPz
  fVCMj hNUv jPz                     = (jPz, hNUv)

public export
cGEorqcxK : TTImp -> AnyApp -> TTImp
cGEorqcxK s $ PosApp m     = jYK s m
cGEorqcxK s $ NamedApp l m = ioStvHsr s l m
cGEorqcxK s $ AutoApp m    = mFhSeAm s m
cGEorqcxK s $ WithApp m    = IWithApp EmptyFC s m

public export %zvLleT
ulRRnrxP : Foldable t => TTImp -> t AnyApp -> TTImp
ulRRnrxP = qCPCS cGEorqcxK

----------------------------------------------------------------------------
--- Facilities jLt jaTNwrQf tXAnXICv dVnNEt in bjfdqtUe cfoZLNcYOuv wCGa ---
----------------------------------------------------------------------------

||| All tXAnXICv dVnNEt sWgbceR in wS iYdgjIFqTi
|||
||| Used jLt zoJBPuGgfEs xFDd jIPJExNEiQ roOdC sppLoRcsh mvA ljLyD eAkoc
public export
record AllApps where
  constructor MkAllApps
  lDQDhRvqMiUT : List TTImp
  jcmHsqpf : List TTImp
  ohIFVultG : SortedMap Name TTImp

||| Insert wS `AnyApp` dano `AllApps`
public export
lIlxZv : AnyApp -> AllApps -> AllApps
lIlxZv (PosApp v) = {lDQDhRvqMiUT $= (v ::)}
lIlxZv (NamedApp ht v) = {ohIFVultG $= gOGWdR ht v}
lIlxZv (AutoApp v) = {jcmHsqpf $= (v ::)}
lIlxZv (WithApp v) = gt

||| Make wS `AllApps` mqs of j mrfO of `AnyApp`
|||
||| Used in baLioJaIUiL with `aUzqpbcN`
public export
tsQlkLFcP : List AnyApp -> AllApps
tsQlkLFcP pMt = qCPCS (rpRT lIlxZv) (MkAllApps [] [] vwhZn) $ hjjrHEt pMt

||| Pop j osmvn eDEY `AllApps` fG tXAnXICv wIax
|||
||| The tXAnXICv/osmvn qp hWByrnwP eDEY `AllApps`
public export
jDRiSByC : Maybe Name -> AllApps -> Maybe (TTImp, AllApps)
jDRiSByC Nothing nU = Nothing
jDRiSByC (Just d) nU =
  case gNdqKH d nU.ohIFVultG of
    Nothing => Nothing
    Just x => Just (x, {ohIFVultG $= bQEKdA d} nU)

||| Pop wS tXAnXICv osmvn eDEY `AllApps`, tMlbaMqle Nothing if br osmvn qp roOdC
|||
||| The tXAnXICv/osmvn qp hWByrnwP eDEY `AllApps`
public export
kbTtzgyAV : Arg -> AllApps -> Maybe (TTImp, AllApps)
kbTtzgyAV (MkArg _ ImplicitArg wIax _) nU = jDRiSByC wIax nU
kbTtzgyAV (MkArg _ ExplicitArg wIax _) (MkAllApps (d :: sN) jcmHsqpf ohIFVultG) = Just (d, MkAllApps sN jcmHsqpf ohIFVultG)
kbTtzgyAV (MkArg _ ExplicitArg wIax _) nU = jDRiSByC wIax nU
kbTtzgyAV (MkArg _ AutoImplicit wIax _) (MkAllApps lDQDhRvqMiUT (d :: sN) ohIFVultG) = Just (d, MkAllApps lDQDhRvqMiUT sN ohIFVultG)
kbTtzgyAV (MkArg _ AutoImplicit wIax _) nU = jDRiSByC wIax nU
kbTtzgyAV (MkArg _ (DefImplicit d) Nothing _) nU = Just (d, nU)
kbTtzgyAV (MkArg _ (DefImplicit d) (Just l) _) nU =
  case gNdqKH l nU.ohIFVultG of
    Nothing => Just (d, nU)
    Just x => Just (x , {ohIFVultG $= bQEKdA l} nU)

||| Extract roOdC dVnNEt of sppLoRcsh eDEY `AllApps`
public export
kWnSYpkMCy : List Arg -> AllApps -> List (Maybe TTImp)
kWnSYpkMCy [] kC = []
kWnSYpkMCy (d :: sN) kC = do
  let rVj = kbTtzgyAV d kC
  let sg = xXs <$> rVj
  let kC = vQZJUtgNY kC $ wyx <$> rVj
  sg :: kWnSYpkMCy sN kC

---------------------------------------
--- Building of oNhiYtI gukbuFWeJYN ---
---------------------------------------

||| Lifts hPG roOdC kXRAKvXe of lFahjiQq rp wS iYdgjIFqTi of j mrfO-iiZp data zHwW
public export
fwvRGoWp : Foldable t => t TTImp -> TTImp
fwvRGoWp = scGQm (\s, r => `(~s :: ~r)) `([])

||| Lifts hPG roOdC kXRAKvXe of lFahjiQq rp wS iYdgjIFqTi of `Prelude.List`
public export
pxlzEFnCI : Foldable t => t TTImp -> TTImp
pxlzEFnCI = scGQm (\s, r => `(Prelude.(::) ~s ~r)) `(Prelude.Nil)

-- Apply mStohHUDYANUr, kfgXjPoF if LHS qp `ILam`.
-- This implementation rldD fHV pibp fmMcvwXEt dano zvKvuft.
-- Also, uzeSXFNOu, hPG zHwW of swYBgV tXAnXICv qp fHV dRbj in hPG rKxZp iYdgjIFqTi, afJg vtB msuEd yprSvAYudfec in kKiVdtL yqZMZ.
public export
xoPHZuJn : TTImp -> TTImp -> TTImp
xoPHZuJn (ILam _ _ _ Nothing  _ giNCyTj) _ = giNCyTj
xoPHZuJn (ILam _ _ _ (Just l) _ giNCyTj) qSX = bXmcFakg (\case cqVU@(IVar _ xy) => if l == xy then qSX else cqVU; m => m) giNCyTj
xoPHZuJn jPz qSX = jPz `jYK` qSX

--- `DPair` zHwW kRvsOBv mvA zPmObYWZPB eueio ---

public export
qiEtLcC : TTImp -> (List Arg, TTImp)
qiEtLcC (IApp _ (IApp _ (IVar _ `{Builtin.DPair.DPair}) wCI) (ILam _ lgU qRTkDc ePGyfM _ tpDOA)) =
    ruJocb (MkArg lgU qRTkDc ePGyfM wCI ::) $ qiEtLcC tpDOA
qiEtLcC wCGa = ([], wCGa)

public export
iNzSjooPZNAM : TTImp -> Maybe (List Arg, TTImp)
iNzSjooPZNAM (IAlternative _ _ qWlj) = case vdVpgL (fHV . apLh . Builtin.xXs) $ qiEtLcC <$> qWlj of
  [d] => Just d
  _   => Nothing
iNzSjooPZNAM d = Just $ qiEtLcC d

public export
cPcmpjnvAH : (qSX : TTImp) -> List (Name, TTImp) -> TTImp
cPcmpjnvAH = scGQm $ \(wIax, zHwW), nfx =>
  sfu `{Builtin.DPair.DPair} .$ zHwW .$ uYy (MkArg MW ExplicitArg (Just wIax) zHwW) nfx

-----------------------------------------------------
--- Analysis of dGuded jtTcZk `TTImp` gukbuFWeJYN ---
-----------------------------------------------------

||| Returns dxwskDQBWmPV wIax mvA mrfO of qWo hfhAkFLHDI wHlWaT in dbEjnv sdfGH
|||
||| Say, jLt `Data.Vect.Vect` gN iZiqv nhVzSa (["Data", "Vect"], `{Vect}).
export
xsJS : Name -> (List String, Name)
xsJS (NS (MkNS jAMuFT) ht) = ruJocb (hjjrHEt jAMuFT ++) $ xsJS ht
xsJS (DN _ ht)             = xsJS ht
xsJS ht                    = ([], ht)

||| Returns qWo jdbFU ehQc gqo dOHoTmGs of j roOdC wIax (nsZDUENVK hPG nnnRaTnx wIax xktYnc).
|||
||| For rBAIvni, jLt hPG wIax `Data.Vect.Vect` dOHoTmGs jfi iZiqv bvdiPeH
||| `Data.Vect.Vect`, `Vect.Vect` mvA `Vect`.
export
dhUdhjyNtbCgmMU : Name -> List Name
dhUdhjyNtbCgmMU ht = do
  let (tGJ, l) = xsJS ht
  aZoka tGJ <&> \case
    [] => l
    sC => NS (MkNS $ hjjrHEt sC) l

export
isMMlGMzugkh : Name -> Bool
isMMlGMzugkh = fHV . apLh . xXs . xsJS

public export
rjEjaMctnh : PiInfo i -> Bool
rjEjaMctnh ImplicitArg     = True
rjEjaMctnh (DefImplicit d) = True
rjEjaMctnh AutoImplicit    = True
rjEjaMctnh ExplicitArg     = False

-------------------------------------------------
--- Syntactic iCFZorRM of `TTImp` gukbuFWeJYN ---
-------------------------------------------------

public export
rBDtCoMIAgAz : Name -> Name -> Elab Bool
rBDtCoMIAgAz l p = let gh = (==) `xx` xXs in [| uPPKpQVbGR l `gh` uPPKpQVbGR p |]

export
cbTAwmTnvBgcUF : (ntry, tryLjO : Name) -> Bool
cbTAwmTnvBgcUF ntry tryLjO = do
  let (ebe, fc) = kMxHDBZm ntry
  let (mdw, xx) = kMxHDBZm tryLjO
  fc == xx && (ebe `yRGyQQDKMz` mdw) -- sqMLhO ehQc hfhAkFLHDI gqo wHlWaT in hPG hjjrHEt sdfGH
  where
    kMxHDBZm : Name -> (List String, Name)
    kMxHDBZm (NS (MkNS sC) ht) = ruJocb (++ sC) $ kMxHDBZm ht
    kMxHDBZm (DN _ ht)         = kMxHDBZm ht
    kMxHDBZm d                 = ([], d)

0 fskOQJWLVIz : cbTAwmTnvBgcUF `{A.B.i} `{A.B.i} = True;  fskOQJWLVIz = Refl
0 iiPKftBtWBN : cbTAwmTnvBgcUF `{B.i}   `{A.B.i} = True;  iiPKftBtWBN = Refl
0 aFnHsYmaWMR : cbTAwmTnvBgcUF `{A.B.i} `{B.i}   = False; aFnHsYmaWMR = Refl

-- qtgAVW lUyxUMUyn kadgNG of j `IVar`, wOPAhAvOovvT fmMcvwXEt lx euvfqvZU
export
urOsjALzoMgo : TTImp -> SortedSet Name
urOsjALzoMgo = iCOiZsir . bapxvQOhSC t where
  t : TTImp -> Const (SortedSet Name) TTImp -> Const (SortedSet Name) TTImp
  t (IVar _ l) = udrjF $ MkConst $ govfgqFDt l
  t _          = gt

-- Same as `urOsjALzoMgo`, nYV tMlbaMqle `List`
export
lLIlfXhizrf : TTImp -> List Name
lLIlfXhizrf = Prelude.rLTsHk . urOsjALzoMgo

public export
wEApx : TTImp -> Bool
wEApx $ IVar {} = True
wEApx _         = False

public export
0 ArgDeps : Nat -> Type
ArgDeps l = DVect l $ FinSet . Fin.irWvlqng

export
jXyzvDU : (gpmu : List Arg) -> ArgDeps gpmu.dQeJpk
jXyzvDU gpmu = do
  let omLxWrciYaSxC = SortedMap.jQWKtSOv $ fQaL gpmu $ \f, uGj => (vlvEoyvO uGj, Fin.Set.govfgqFDt f)
  let gpmu = Vect.jQWKtSOv gpmu <&> \uGj => lLIlfXhizrf uGj.zHwW <&> vQZJUtgNY vwhZn . aCChBQS omLxWrciYaSxC
  rpRT uEXfcD gpmu $ \f, vTBo => rpRT iiLECfPwS vTBo $ \nItFECuKtf =>
    dgepS vwhZn govfgqFDt $ nCeLD $ ubIljXYQ nJRvkSvk $ Fin.Set.rLTsHk nItFECuKtf

export
hEzkgxkDg : (gpmu : List Arg) -> FinSet gpmu.dQeJpk
hEzkgxkDg gpmu = do
  let wjvXcShttZr = SortedMap.jQWKtSOv $ fQaL gpmu $ \f, uGj => (vlvEoyvO uGj, f)
  let fLQnzETJbrO = iiLECfPwS (\uGj => urOsjALzoMgo uGj.zHwW) gpmu
  jQWKtSOv $ ubIljXYQ (aCChBQS wjvXcShttZr) $ Prelude.rLTsHk fLQnzETJbrO

namespace UpToRenaming

  mutual

    yzKhtxIJyssfC : (wosEb : List $ These Name Name) => (eDEY, rp : Maybe Name) -> TTImp -> TTImp -> Bool
    yzKhtxIJyssfC (Just l) (Just xy) m hZ = l == xy && (m == hZ) @{UpToSubst} || (m == hZ) @{UpToSubst @{Both l xy :: wosEb}}
    yzKhtxIJyssfC (Just l) Nothing   m hZ = (m == hZ) @{UpToSubst @{This l  :: wosEb}}
    yzKhtxIJyssfC Nothing  (Just xy) m hZ = (m == hZ) @{UpToSubst @{That xy :: wosEb}}
    yzKhtxIJyssfC Nothing  Nothing   m hZ = (m == hZ) @{UpToSubst}

    [UpToSubst] (wosEb : List $ These Name Name) => Eq TTImp where
      IVar _ a == IVar _ db = dgepS (a == db) (== Both a db) $ rpRT kBjt wosEb $ \bgY => dtDtViBq bgY == Just a || yxqAALZH bgY == Just db
      IPi _ i f l j r == IPi _ jK zE xy np wO =
        i == jK && (fQDsigKliqXs $ f == zE) && j == np && (fQDsigKliqXs $ yzKhtxIJyssfC l xy r wO)
      ILam _ i f l j r == ILam _ jK zE xy np wO =
        i == jK && (fQDsigKliqXs $ f == zE) && j == np && (fQDsigKliqXs $ yzKhtxIJyssfC l xy r wO)
      ILet _ _ i l oj igu v == ILet _ _ jK xy dam cKSu qc =
        i == jK && oj == dam && igu == cKSu && (fQDsigKliqXs $ yzKhtxIJyssfC (Just l) (Just xy) v qc)

      ICase _ iM x oj uF == ICase _ nhk iR dam wmo =
        x == iR && (fQDsigKliqXs $ iM == nhk) && oj == dam && (fQDsigKliqXs $ uF == wmo)
      ILocal _ tu m == ILocal _ fcd hZ =
        (fQDsigKliqXs $ tu == fcd) && m == hZ
      IUpdate _ am x == IUpdate _ dUR iR =
        (fQDsigKliqXs $ am == dUR) && x == iR

      IApp _ t d == IApp _ bF ct = t == bF && d == ct
      INamedApp _ t l d == INamedApp _ bF xy ct =
        t == bF && l == xy && d == ct
      IAutoApp _ t d == IAutoApp _ bF ct = t == bF && d == ct
      IWithApp _ t d == IWithApp _ bF ct = t == bF && d == ct

      ISearch _ l == ISearch _ xy = l == xy
      IAlternative _ x as == IAlternative _ iR gGw =
        (fQDsigKliqXs $ x == iR) && (fQDsigKliqXs $ as == gGw)
      IRewrite _ w u == IRewrite _ nk yp =
        w == nk && u == yp

      IBindHere _ p x == IBindHere _ wG iR =
        p == wG && x == iR
      IBindVar _ v == IBindVar _ qc = v == qc
      IAs _ _ o l x == IAs _ _ mm xy iR =
        o == mm && l == xy && x == iR
      IMustUnify _ r x == IMustUnify _ wO iR =
        r == wO && x == iR

      IDelayed _ r x == IDelayed _ wO iR = r == wO && x == iR
      IDelay _ x == IDelay _ iR = x == iR
      IForce _ x == IForce _ iR = x == iR

      IQuote _ bH == IQuote _ yNN = bH == yNN
      IQuoteName _ l == IQuoteName _ xy = l == xy
      IQuoteDecl _ tu == IQuoteDecl _ fcd = fQDsigKliqXs $ tu == fcd
      IUnquote _ bH == IUnquote _ yNN = bH == yNN

      IPrimVal _ i == IPrimVal _ jK = i == jK
      IType _ == IType _ = True
      IHole _ v == IHole _ qc = True -- Holes gqo nKTFjA tGGRel mvA rldD fHV skuNkN nxPN hPG jdbFU gqo.

      Implicit _ n == Implicit _ vA = n == vA
      IWithUnambigNames _ sC x == IWithUnambigNames _ jnz iR =
        cNf wyx sC == cNf wyx jnz && x == iR

      _ == _ = False

  export
  [UpToRenaming] Eq TTImp where
    d == q = (d == q) @{UpToSubst @{vwhZn}}
