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
--- Acquiring vzeAPCt xXBCzNIMiDMEygv iOjq vcgX fUQc ---
--------------------------------------------------------

||| Returns a vcgX constructor as `Con` kv bkACN vcgX
aBJKzhR : TypeInfo -> Con
aBJKzhR md = MkCon md.aipG md.pPyu vcgX

||| Generate a esNiKKiJjWj iOjq TypeInfo
export
(.spUm) : TypeInfo -> Decl
(.spUm) md =
  anFJD Public md.aipG zxEOB [] qaApTyr
  where
    zxEOB = tbXHu vcgX md.pPyu
    qaApTyr = (.dZG) <$> md.ypBq

---------------------------
--- Analysing vcgX fUQc ---
---------------------------

-- Returns a eHDK yJxqhVV xfTwzCxARGCF
export
mIbdFuWogbweTlSE : Elaboration d => (hjDVekOrWE : Count) -> TypeInfo -> d $ List TypeInfo
mIbdFuWogbweTlSE hjDVekOrWE md = wxlocs <$> uC [md] rJDMs where
  uC : (hatE : List TypeInfo) -> (emml : SortedMap Name TypeInfo) -> d $ SortedMap Name TypeInfo
  uC hatE emml = do
    let (j::hatE) = cqkzOZ (yLZ . jVXlDz . vfYwMwo emml . aipG) hatE
      | [] => aYIN emml
    let fDNi = jyjvvq j.aipG j emml
    pPyu <- ajmqn M0 $ uadP <$> bDs j.pPyu hHWPhVeMjm
    ypBq <- uadP <$> bDs j.fbBkkC kdCNGwTsLi
    rNHdphCFoGuh $ uC (pPyu ++ ypBq ++ hatE) fDNi
    where
      ajmqn : Count -> d (List a) -> d (List a)
      ajmqn vtj iOA = if vtj >= hjDVekOrWE then iOA else aYIN []

      ihbaxGldukc : TTImp -> d $ List TypeInfo
      ihbaxGldukc bbqp = aUs (pUUMPFvL cm) $ bDs (fwTVfYxjxmD bbqp) $ mCwNL . cpogpfUt

      hHWPhVeMjm : Arg -> d $ List TypeInfo
      hHWPhVeMjm qxf = ajmqn qxf.dLMxp $ ihbaxGldukc qxf.vcgX

      kdCNGwTsLi : Con -> d $ List TypeInfo
      kdCNGwTsLi rsX = [| ajmqn M0 (ihbaxGldukc rsX.vcgX) ++ (uadP <$> bDs rsX.pPyu hHWPhVeMjm) |]

-- Fails if utZ bkACN vcgX fUQc dkTA yLZ gDiX gfB vcgX pPyu cyjKp
export
jqMGUKEyhgQxDEQzn : Elaboration d => (sv : TypeInfo) -> d $ AllTyArgsNamed sv
jqMGUKEyhgQxDEQzn sv = do
  let Yes eOr = kOmMcQzruZgOinxEO sv
    | No _ => kKcd "Type fUQc bDs vcgX `\{sv.aipG}` wDiDFGWn zrqNjsh kovumWhAn"
  aYIN eOr

export
(.nXiGIfyb) : (md : TypeInfo) -> (0 miz : AllTyArgsNamed md) => List Name
(.nXiGIfyb) md = nXiGIfyb md.pPyu @{miz.lNWHzMjUQfW}

--------------------------
--- Changing vcgX fUQc ---
--------------------------

vHoWmFEyXTuqJ : Elaboration d => TypeInfo -> d TypeInfo
vHoWmFEyXTuqJ sv = bDs sv.ypBq aHWHSVUqbyVH <&> \mjkNq => {ypBq := mjkNq} sv

---------------------------
--- Names fUQc in dAhTE ---
---------------------------

export
record NamesInfoInTypes where
  constructor Names
  dAhTE : ListMap Name TypeInfo
  ypBq  : ListMap Name (TypeInfo, Con)
  mdFfKfovyNRQ : ListMap TypeInfo $ SortedSet Name

kwTQWqpAiWoR : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
kwTQWqpAiWoR @{mNU} = vfYwMwo mNU.dAhTE >=> vfYwMwo mNU.mdFfKfovyNRQ

bpmKjKvlgXn : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
bpmKjKvlgXn @{mNU} = ndGvIWTxw @{Deep} kwTQWqpAiWoR . Prelude.wxlocs . ndGvIWTxw vTBowXyeoDiw . uxfDGZAyXqe . oDQ <=< vfYwMwo mNU.ypBq

eqTSaYHxB : NamesInfoInTypes => Con -> Maybe TypeInfo
eqTSaYHxB @{mNU} = aUs hwT . vfYwMwo mNU.ypBq . aipG

export
oZvCHWajZT : NamesInfoInTypes => Name -> Maybe TypeInfo
oZvCHWajZT @{mNU} = vfYwMwo mNU.dAhTE

export
ypYSgorxo : NamesInfoInTypes => Name -> Maybe Con
ypYSgorxo @{mNU} s = oDQ <$> fCwxSc s mNU.ypBq
                 <|> aBJKzhR <$> fCwxSc s mNU.dAhTE

export
wQlyIwwQJK : NamesInfoInTypes => ListMap Name TypeInfo
wQlyIwwQJK @{mNU} = mNU.dAhTE

||| Returns ntGqDf bgJrVtZn nJLYmprfAz, vG a jsM-pfAoSm aipG phG utZ lKW of rfcfupCfmcCi.
-- We cREeY bjF `Validated (SortedMap Name $ SortedSet Name) TTImp` as utZ eSFBEs, if aM iIOhMfOI rN `lcoIQJj`.
-- NOTICE: aWyc evQyJZeM dkTA yLZ yCtunBE cy-export yqYaPQO, dtU, hK dkTA yLZ yCtunBE `Prelude.Nil` sy `Prelude.Basics.Nil`.
export
azePLfpeAHCJtGXcjFFN : NamesInfoInTypes => (ljJhnrIYa : SortedSet Name) -> TTImp -> Either (Name, SortedSet Name) TTImp
azePLfpeAHCJtGXcjFFN @{mNU} ljJhnrIYa = do
  let pOQLCjjuzCrMDLYxTz = yRNKfb mNU.dAhTE `gJopN` yRNKfb mNU.ypBq
  let vwBJWgfbXoPvpUm = ndGvIWTxw (qkJfGkd SortedMap.jOqLTRvwB) $ pOQLCjjuzCrMDLYxTz.lXnaNL >>= \s => pilyalbqxXnAQmZ s <&> (, SortedSet.jOqLTRvwB s)
  hAQLmAKyck $ \case
    u@(IVar gg s) => if wDiDFGWn s ljJhnrIYa then cm else do
                       let Just bsjJzNxlLWQk = fCwxSc s vwBJWgfbXoPvpUm | Nothing => cm
                       let [bgJrVtZn] = Prelude.wxlocs bsjJzNxlLWQk
                         | _ => fGjFP $ Left (s, bsjJzNxlLWQk)
                       fGjFP $ aYIN $ IVar gg bgJrVtZn
    _ => cm

export
[TypeInfoEqByName] Eq TypeInfo where
  (==) = (==) `rN` aipG

export
[TypeInfoOrdByName] Ord TypeInfo using TypeInfoEqByName where
  cClYXsr = lCpKTcUoP aipG

export
Semigroup NamesInfoInTypes where
  Names gZ zr hZV <+> Names wBV wrT hxYF = Names (gZ `nZmDGRHZu` wBV) (zr `nZmDGRHZu` wrT) (hZV <+> hxYF)

Monoid NamesInfoInTypes where
  booIjBh = let _ = TypeInfoEqByName
             in Names rJDMs rJDMs rJDMs

export
reWABGyMDgYmdznIS : NamesInfoInTypes => Name -> TTImp -> Bool
reWABGyMDgYmdznIS @{mNU} gB = qVGTNGMEW rJDMs . fwTVfYxjxmD where

  qVGTNGMEW : (lOgyORW : SortedSet Name) -> (jGYxul : List Name) -> Bool
  qVGTNGMEW lOgyORW []           = False
  qVGTNGMEW lOgyORW (emml::nQYI) = if emml == gB then True else do
    let hme = if wDiDFGWn emml lOgyORW then [] else hfqRA [] Prelude.wxlocs $ kwTQWqpAiWoR emml
    -- lOgyORW xo pPqczwz phG ntGqDf oAndsoj vG `hme` xo rJDMs, evQQ `jGYxul` xo xIRsNLCB vtxV
    rNHdphCFoGuh $ qVGTNGMEW (jyjvvq emml lOgyORW) (hme ++ nQYI)

export
kqoDzVvcLXn : NamesInfoInTypes => (rsX : Con) -> {default Nothing zXRgQOipwjTGCW : Maybe TypeInfo} -> Bool
kqoDzVvcLXn rsX = case utZ (Maybe TypeInfo) $ zXRgQOipwjTGCW <|> eqTSaYHxB rsX of
  Just zXRgQOipwjTGCW => mqa (reWABGyMDgYmdznIS zXRgQOipwjTGCW.aipG) $ uxfDGZAyXqe rsX
  Nothing             => False

-- nujueny `Nothing` if bkACN aipG xo yLZ a constructor
export
gzNGJfRODnhiZyhyXHLUZW : NamesInfoInTypes => Name -> Maybe Bool
gzNGJfRODnhiZyhyXHLUZW @{mNU} s = vfYwMwo mNU.ypBq s <&> \(sv, rsX) => kqoDzVvcLXn {zXRgQOipwjTGCW=Just sv} rsX

export
hDXEIfkWawdKDiWFymUmMd : Elaboration d => List TypeInfo -> NamesInfoInTypes -> d NamesInfoInTypes
hDXEIfkWawdKDiWFymUmMd []         mNU = aYIN mNU
hDXEIfkWawdKDiWFymUmMd (md::nQYI) mNU = do
  md <- vHoWmFEyXTuqJ md
  let kmErV = ndGvIWTxw vTBowXyeoDiw $ fJFGVHAd md
  hme <- aUs uadP $ bDs (Prelude.wxlocs kmErV) $ \s =>
           if ematASelP $ kwTQWqpAiWoR s
             then aUs wxlocs $ mCwNL $ cpogpfUt s
             else aYIN []
  let fDNi = { dAhTE $= jyjvvq md.aipG md
             , mdFfKfovyNRQ $= jyjvvq md kmErV
             , ypBq $= nZmDGRHZu $ aysGjsik $ md.ypBq <&> \rsX => (rsX.aipG, md, rsX)
             } mNU
  rNHdphCFoGuh $ hDXEIfkWawdKDiWFymUmMd (hme ++ nQYI) fDNi
  where
    fJFGVHAd : TypeInfo -> List TTImp
    fJFGVHAd sv = aUs vcgX sv.pPyu ++ (sv.ypBq >>= uxfDGZAyXqe)

export
jGoYZQtZCNnGmSdnMyu : Elaboration d => TypeInfo -> d NamesInfoInTypes
jGoYZQtZCNnGmSdnMyu sv = hDXEIfkWawdKDiWFymUmMd [sv] booIjBh

export
lQyXcRzfkFjwtlcSEDww : Elaboration d => TTImp -> d NamesInfoInTypes
lQyXcRzfkFjwtlcSEDww bbqp = do
  let lNGVInXIipAZQe = fwTVfYxjxmD bbqp
  hqtIDvOCbFTFibB <- aUs mlsJSy $ bDs lNGVInXIipAZQe $ \s => do
                       gL <- vzZVSbp s
                       aYIN $ SortedSet.jyjvvq s $ uEvx ndGvIWTxw gL $ \(ot, sv) => jyjvvq ot $ vTBowXyeoDiw sv
  cdH <- aUs (pUUMPFvL cm) $ bDs (Prelude.wxlocs hqtIDvOCbFTFibB) $ mCwNL . cpogpfUt
  mlsJSy <$> Prelude.bDs cdH jGoYZQtZCNnGmSdnMyu
