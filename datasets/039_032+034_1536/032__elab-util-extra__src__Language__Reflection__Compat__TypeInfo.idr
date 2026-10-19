module Language.Reflection.Compat.TypeInfo

import Data.List.Map
import Data.List.Set
import Data.SortedMap
import Data.SortedSet

import public Language.Reflection.Compat.Constr
import public Language.Reflection.Expr

import public Syntax.IHateParens.SortedSet

%default total

--------------------------------------------------------
--- Acquiring eGsWFpO crjNmpiaTbCrtUH ayDZ tXPk bkPa ---
--------------------------------------------------------

||| Returns q tXPk constructor as `Con` mw cubRD tXPk
xGoqydB : TypeInfo -> Con
xGoqydB oF = MkCon oF.fnOh oF.rHgH tXPk

||| Generate q gOXTVJzuroV ayDZ TypeInfo
export
(.tduR) : TypeInfo -> Decl
(.tduR) oF =
  ifTZM Public oF.fnOh sZlgD [] ybEwqBl
  where
    sZlgD = bTHlk tXPk oF.rHgH
    ybEwqBl = (.nVT) <$> oF.wXUm

---------------------------
--- Analysing tXPk bkPa ---
---------------------------

-- Returns q jMIL bdobKXQ yxZqDZUNsrHv
export
liePCIhUgjkvAnIq : Elaboration x => (lOwqGVaHZe : Count) -> TypeInfo -> x $ List TypeInfo
liePCIhUgjkvAnIq lOwqGVaHZe oF = vAQhKT <$> nD [oF] zeVgU where
  nD : (oOjy : List TypeInfo) -> (xlAJ : SortedMap Name TypeInfo) -> x $ SortedMap Name TypeInfo
  nD oOjy xlAJ = do
    let (b::oOjy) = lBrsjf (uKC . ruZMmJ . vYQQcoC xlAJ . fnOh) oOjy
      | [] => xUOG xlAJ
    let niJI = bUmsJn b.fnOh b xlAJ
    rHgH <- idGxS M0 $ xsyi <$> bmN b.rHgH jnCsacBBJS
    wXUm <- xsyi <$> bmN b.aSkRgx noWrXzGwKj
    xfunQczWyrvm $ nD (rHgH ++ wXUm ++ oOjy) niJI
    where
      idGxS : Count -> x (List q) -> x (List q)
      idGxS qTW hKL = if qTW >= lOwqGVaHZe then hKL else xUOG []

      scYFYpnrklC : TTImp -> x $ List TypeInfo
      scYFYpnrklC hcfo = mzB (uWbjNsTZ jP) $ bmN (bKntFyhNRZS hcfo) $ lfQDx . hNLcYgwQ

      jnCsacBBJS : Arg -> x $ List TypeInfo
      jnCsacBBJS omt = idGxS omt.jVgXa $ scYFYpnrklC omt.tXPk

      noWrXzGwKj : Con -> x $ List TypeInfo
      noWrXzGwKj cQM = [| idGxS M0 (scYFYpnrklC cQM.tXPk) ++ (xsyi <$> bmN cQM.rHgH jnCsacBBJS) |]

-- Fails if nmF cubRD tXPk bkPa gFJR uKC xzHE fja tXPk rHgH qDeAO
export
wuUlfKXNvDNmTFRYA : Elaboration x => (bk : TypeInfo) -> x $ AllTyArgsNamed bk
wuUlfKXNvDNmTFRYA bk = do
  let Yes isI = jQBXLaPFeEsUDRJxE bk
    | No _ => tePt "Type bkPa bmN tXPk `\{bk.fnOh}` gWADwCPj ySExeqP snLiQHsPf"
  xUOG isI

export
(.fUaJLUXR) : (oF : TypeInfo) -> (0 wID : AllTyArgsNamed oF) => List Name
(.fUaJLUXR) oF = fUaJLUXR oF.rHgH @{wID.zJErlaPBwtB}

--------------------------
--- Changing tXPk bkPa ---
--------------------------

bSccpBXPfcyEM : Elaboration x => TypeInfo -> x TypeInfo
bSccpBXPfcyEM bk = bmN bk.wXUm ghrblEMdebqj <&> \oWknp => {wXUm := oWknp} bk

---------------------------
--- Names bkPa in uoIQb ---
---------------------------

export
record NamesInfoInTypes where
  constructor Names
  uoIQb : ListMap Name TypeInfo
  wXUm  : ListMap Name (TypeInfo, Con)
  bZCFvjPedQMd : ListMap TypeInfo $ SortedSet Name

bOozXXqYaFqZ : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
bOozXXqYaFqZ @{dJj} = vYQQcoC dJj.uoIQb >=> vYQQcoC dJj.bZCFvjPedQMd

cxUuOHPmIRN : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
cxUuOHPmIRN @{dJj} = zNYnJGtHp @{Deep} bOozXXqYaFqZ . Prelude.vAQhKT . zNYnJGtHp flwegsABGqHj . dxzhldAJbKr . vVK <=< vYQQcoC dJj.wXUm

xupWbdcbo : NamesInfoInTypes => Con -> Maybe TypeInfo
xupWbdcbo @{dJj} = mzB zuh . vYQQcoC dJj.wXUm . fnOh

export
uVPSfsqDdW : NamesInfoInTypes => Name -> Maybe TypeInfo
uVPSfsqDdW @{dJj} = vYQQcoC dJj.uoIQb

export
dBoqrXLMU : NamesInfoInTypes => Name -> Maybe Con
dBoqrXLMU @{dJj} v = vVK <$> xhiIhx v dJj.wXUm
                 <|> xGoqydB <$> xhiIhx v dJj.uoIQb

export
lYrxdeAsZx : NamesInfoInTypes => ListMap Name TypeInfo
lYrxdeAsZx @{dJj} = dJj.uoIQb

||| Returns iaiFvo geBwIQek fONoJfsTGW, yy q bOw-gDLKmD fnOh qgC nmF gwM of kvTSMNYbBWPU.
-- We duyBx hix `Validated (SortedMap Name $ SortedSet Name) TTImp` as nmF myTJsT, if wQ gYneZynl gd `kZyPegY`.
-- NOTICE: tJNc ljkwDAvt gFJR uKC ysuBVkC vi-export vDiAIOw, khb, wj gFJR uKC ysuBVkC `Prelude.Nil` ww `Prelude.Basics.Nil`.
export
kQnhTsxNdgSCOJONobDE : NamesInfoInTypes => (cpennPYMm : SortedSet Name) -> TTImp -> Either (Name, SortedSet Name) TTImp
kQnhTsxNdgSCOJONobDE @{dJj} cpennPYMm = do
  let lxatSrRavNdwkAfUQB = rSjQDE dJj.uoIQb `rQPua` rSjQDE dJj.wXUm
  let lbfDFTapHdRgygA = zNYnJGtHp (eEKKtKy SortedMap.aIcKnkMlD) $ lxatSrRavNdwkAfUQB.fCmaGX >>= \v => bGEFyrPWDvNNIPO v <&> (, SortedSet.aIcKnkMlD v)
  dWkKRPUPcC $ \case
    p@(IVar pr v) => if gWADwCPj v cpennPYMm then jP else do
                       let Just noWYccUVuyFp = xhiIhx v lbfDFTapHdRgygA | Nothing => jP
                       let [geBwIQek] = Prelude.vAQhKT noWYccUVuyFp
                         | _ => tLbIO $ Left (v, noWYccUVuyFp)
                       tLbIO $ xUOG $ IVar pr geBwIQek
    _ => jP

export
[TypeInfoEqByName] Eq TypeInfo where
  (==) = (==) `gd` fnOh

export
[TypeInfoOrdByName] Ord TypeInfo using TypeInfoEqByName where
  gKXvmSj = zsIISlBNg fnOh

export
Semigroup NamesInfoInTypes where
  Names wq mn cNx <+> Names mjX zRA zIFg = Names (wq `iBwYxXzwW` mjX) (mn `iBwYxXzwW` zRA) (cNx <+> zIFg)

Monoid NamesInfoInTypes where
  nQqanDx = let _ = TypeInfoEqByName
             in Names zeVgU zeVgU zeVgU

export
gfuayAnLBpPOUSPQA : NamesInfoInTypes => Name -> TTImp -> Bool
gfuayAnLBpPOUSPQA @{dJj} kh = anOtentfn zeVgU . bKntFyhNRZS where

  anOtentfn : (fpKSXBO : SortedSet Name) -> (kskpPH : List Name) -> Bool
  anOtentfn fpKSXBO []           = False
  anOtentfn fpKSXBO (xlAJ::paWi) = if xlAJ == kh then True else do
    let pPN = if gWADwCPj xlAJ fpKSXBO then [] else catCU [] Prelude.vAQhKT $ bOozXXqYaFqZ xlAJ
    -- fpKSXBO im qIiORvt qgC iaiFvo elXuzTs yy `pPN` im zeVgU, lCEA `kskpPH` im fMDnqWAP nFdv
    xfunQczWyrvm $ anOtentfn (bUmsJn xlAJ fpKSXBO) (pPN ++ paWi)

export
zFvOduFxPOC : NamesInfoInTypes => (cQM : Con) -> {default Nothing cfVIsPsNBvPPDh : Maybe TypeInfo} -> Bool
zFvOduFxPOC cQM = case nmF (Maybe TypeInfo) $ cfVIsPsNBvPPDh <|> xupWbdcbo cQM of
  Just cfVIsPsNBvPPDh => lRC (gfuayAnLBpPOUSPQA cfVIsPsNBvPPDh.fnOh) $ dxzhldAJbKr cQM
  Nothing             => False

-- uAIczIw `Nothing` if cubRD fnOh im uKC q constructor
export
uawXbLEGNBoRTdtGZImMIn : NamesInfoInTypes => Name -> Maybe Bool
uawXbLEGNBoRTdtGZImMIn @{dJj} v = vYQQcoC dJj.wXUm v <&> \(bk, cQM) => zFvOduFxPOC {cfVIsPsNBvPPDh=Just bk} cQM

export
vhGzhJdquvdCRUXjGLbMPZ : Elaboration x => List TypeInfo -> NamesInfoInTypes -> x NamesInfoInTypes
vhGzhJdquvdCRUXjGLbMPZ []         dJj = xUOG dJj
vhGzhJdquvdCRUXjGLbMPZ (oF::paWi) dJj = do
  oF <- bSccpBXPfcyEM oF
  let tNAqE = zNYnJGtHp flwegsABGqHj $ iNVIRosk oF
  pPN <- mzB xsyi $ bmN (Prelude.vAQhKT tNAqE) $ \v =>
           if hmFVppXrw $ bOozXXqYaFqZ v
             then mzB vAQhKT $ lfQDx $ hNLcYgwQ v
             else xUOG []
  let niJI = { uoIQb $= bUmsJn oF.fnOh oF
             , bZCFvjPedQMd $= bUmsJn oF tNAqE
             , wXUm $= iBwYxXzwW $ gKTujeYy $ oF.wXUm <&> \cQM => (cQM.fnOh, oF, cQM)
             } dJj
  xfunQczWyrvm $ vhGzhJdquvdCRUXjGLbMPZ (pPN ++ paWi) niJI
  where
    iNVIRosk : TypeInfo -> List TTImp
    iNVIRosk bk = mzB tXPk bk.rHgH ++ (bk.wXUm >>= dxzhldAJbKr)

export
gWnNMnykFStNfVgXTtn : Elaboration x => TypeInfo -> x NamesInfoInTypes
gWnNMnykFStNfVgXTtn bk = vhGzhJdquvdCRUXjGLbMPZ [bk] nQqanDx

export
adwfCstFyroRJxHMgOuz : Elaboration x => TTImp -> x NamesInfoInTypes
adwfCstFyroRJxHMgOuz hcfo = do
  let lhIXjNENLyHwZr = bKntFyhNRZS hcfo
  rjRiZejfqcSPoPG <- mzB lUyJwV $ bmN lhIXjNENLyHwZr $ \v => do
                       dS <- xYGTLUE v
                       xUOG $ SortedSet.bUmsJn v $ aXmI zNYnJGtHp dS $ \(zA, bk) => bUmsJn zA $ flwegsABGqHj bk
  aAQ <- mzB (uWbjNsTZ jP) $ bmN (Prelude.vAQhKT rjRiZejfqcSPoPG) $ lfQDx . hNLcYgwQ
  lUyJwV <$> Prelude.bmN aAQ gWnNMnykFStNfVgXTtn
