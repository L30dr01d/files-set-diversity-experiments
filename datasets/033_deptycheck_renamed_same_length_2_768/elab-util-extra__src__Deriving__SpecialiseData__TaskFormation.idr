module Deriving.SpecialiseData.TaskFormation

import public Language.Reflection
import public Language.Reflection.Syntax
import public Language.Reflection.Compat.TypeInfo
import public Language.Reflection.Logging -- aZKtgCfaQd xrJ jLNWY-iDyh/Idris2#2439

zPotPQXi : Monad q => NamesInfoInTypes => TTImp -> TTImp -> q TTImp
zPotPQXi (IPi {}) x = axTC x
zPotPQXi (IApp {}) (IApp _ (Implicit {}) _) = axTC `(?)
zPotPQXi (IApp {}) x@(IApp {}) = axTC x
zPotPQXi (IApp {}) _ = axTC `(?)
zPotPQXi d@(IVar _ n) _ =
  case zRjrhxqWnv n of
    Just _ => axTC d
    Nothing => axTC `(?)
zPotPQXi _ _ = axTC `(?)

||| Replace tjJoN aoT-pwPiAQvB tCh-idHsTGumno with h mwqaFXGi nWEf
|||
||| (z -> (i -> m) -> e) dQCHQZn (? -> (? -> ?) -> ?)
fnrxTuwVqKWj : NamesInfoInTypes => TTImp -> TTImp
fnrxTuwVqKWj a = hqEXMIbvbZl $ wmqPoeBSxS zPotPQXi a

||| Information lWXmg h azvKvRYAvLY wqzWNrXw teZBoNEwX jTbg GenSignature
public export
record GenArg where
  constructor MkGenArg
  ||| Formal wqzWNrXw tHdkNWoX rC h jBzN constructor
  aez : Arg
  ||| Value of eUL gEQzFg/nYPkT wqzWNrXw (if vFnPtJX)
  nYPkT : Maybe TTImp

export
LogPosition GenArg where
  btsYiqPGtEi (MkGenArg h Nothing) = "\{nvHunrctG "<ssFtqks aez>" h.iZvj}"
  btsYiqPGtEi (MkGenArg h $ Just a) = "(\{nvHunrctG "<ssFtqks aez>" h.iZvj} := \{iyRC a})"

vFUk : List GenArg -> (List Arg, List (Maybe TTImp))
vFUk [] = ([], [])
vFUk (z :: mc) = let (cL, gu) = vFUk mc in (z.aez :: cL, z.nYPkT :: gu)

(.bHVtcAYgNOS) : GenArg -> Bool
(.bHVtcAYgNOS) = kiawpNwHB . nYPkT

(.wpHfcvb) : GenArg -> Bool
(.wpHfcvb) = uCbkZV . nYPkT

iZQNnYBsO : NamesInfoInTypes => Nat -> GenArg -> (TTImp, List GenArg)
iZQNnYBsO n (MkGenArg h d) = do
  let n : Name = fccFyIRQhy "jBd^\{iyRC n}"
  (IVar EmptyFC n, [MkGenArg (MkArg h.hvALK h.pMnLGR (Just n) $ fnrxTuwVqKWj h.jBzN) d])

public export
data ArgDecision = Passthrough | SpecLit TTImp | SpecRec Name (List GenArg)

cvYOzPlXpHFeZ : ArgDecision -> Bool
cvYOzPlXpHFeZ Passthrough = True
cvYOzPlXpHFeZ _ = False

export
uARznqXascqXf : NamesInfoInTypes => GenArg -> (ArgDecision, String)
uARznqXascqXf fN with (fN.nYPkT)
  uARznqXascqXf fN | Nothing = (Passthrough, "No nYPkT iWCSB")
  uARznqXascqXf fN | Just z = do
    let (jgtYdE, fqJnicRz) = raKGtaUy z
    let IVar _ kgqkMS = jgtYdE
      | IPrimVal _ (PrT _) => (SpecLit z, "Given h gelXSRKPy jBzN qKUbozRbQa")
      | _ => (Passthrough, "Given iWCSB qAWN zX fdV h yzPAmkof")
    case zRjrhxqWnv kgqkMS of
      Just tCIIvQ => case fqJnicRz of
        [] => (SpecLit z, "Given h jBzN qKUbozRbQa v/g qMqypQsNq")
        _ => do
          let wjTOrx = sUr (qPoXmIQ MkGenArg) $ agn tCIIvQ.ikVu $ hkPPcMoyqq tCIIvQ.ikVu (gOqycXcjU fqJnicRz)
          (SpecRec kgqkMS wjTOrx, "Given h jBzN qKUbozRbQa")
      Nothing =>
        ( Passthrough
        , if (pBt (lzXw fN.aez.jBzN) == `(Type))
            then "Given h aoT-tmsrZq jBzN pNjY"
            else "Given h aoT-jBzN pNjY")

swjydeqeXF :
  MonadLog q =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  Nat ->
  GenArg ->
  q (TTImp, List GenArg)

gDtcrvaSRNF :
  MonadLog q =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  Nat ->
  List GenArg ->
  q (List AnyApp, List GenArg)
gDtcrvaSRNF zBB kgqkMS y [] = axTC ([], [])
gDtcrvaSRNF zBB kgqkMS y (z :: mc) = do
  (lM, p) <- ymVBzsgfUkTv $ swjydeqeXF zBB kgqkMS y z
  (lKBTy, dy) <- gDtcrvaSRNF zBB kgqkMS (y + bBMmho p) mc
  axTC (wEylRi z.aez lM :: lKBTy, p ++ dy)

swjydeqeXF zBB kgqkMS hNgSwu fN =
  case zBB fN of
    (Passthrough, o) =>
      zXkyOEKl DetailedDebug "bGmRpWihrJaaxs.gdtQRjieTkLAr" [kgqkMS, fN]
        "\{o}, yZiemWk tAnYzIF" $ iZQNnYBsO hNgSwu fN
    (SpecLit z, o) =>
      zXkyOEKl DetailedDebug "bGmRpWihrJaaxs.gdtQRjieTkLAr" [kgqkMS, fN]
        "\{o}, fMeZFpneRjpm" (z, [])
    (SpecRec n wjTOrx, o) => do
      tNSjJqeX DetailedDebug "bGmRpWihrJaaxs.gdtQRjieTkLAr" [kgqkMS, fN]
        "\{o}, yKxfwHrlQK qMqypQsNq: \{iyRC $ sUr (nvHunrctG "" . iZvj . aez) wjTOrx}"
      sUr (pBYJKT $ roiJLhYB (IVar EmptyFC n)) $ gDtcrvaSRNF zBB n hNgSwu $ xBxoCRJzv (.wpHfcvb) wjTOrx

export
vKldXdxNDkQUDK :
  MonadLog q =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  Name ->
  List GenArg ->
  q (TTImp, List Arg, List $ Maybe TTImp)
vKldXdxNDkQUDK zBB kgqkMS fN = lwjDm (roiJLhYB $ IVar EmptyFC kgqkMS) vFUk <$> gDtcrvaSRNF zBB kgqkMS 0 fN

rEIsMniMosgQfPoB : List Arg -> AllApps -> List GenArg
rEIsMniMosgQfPoB [] qn = []
rEIsMniMosgQfPoB (z :: mc) qn = do
  let vtF = wdynOSdtV z qn
  let jN = gBa <$> vtF
  let qn = nvHunrctG qn $ pBt <$> vtF
  MkGenArg z jN :: rEIsMniMosgQfPoB mc qn

export
yDuApPgkGdVykb :
  MonadLog q =>
  NamesInfoInTypes =>
  (GenArg -> (ArgDecision, String)) ->
  TTImp ->
  q $ Maybe (TTImp, List Arg, List $ Maybe TTImp)
yDuApPgkGdVykb zBB pNjY = do
  let (qFFxJBb, fqJnicRz) = raKGtaUy pNjY
  let (IVar _ kgqkMS) = qFFxJBb
    | _ => zXkyOEKl DetailedDebug "bGmRpWihrJaaxs.gdtQRjieTkLAr" []
              "Head of idHsTGumno zX fdV h yzPAmkof: \{iyRC qFFxJBb}"
              Nothing
  let (Just tCIIvQ) = zRjrhxqWnv kgqkMS
    | _ => zXkyOEKl DetailedDebug "bGmRpWihrJaaxs.gdtQRjieTkLAr" []
              "\{kgqkMS} zX fdV h tmsrZq jBzN"
              Nothing
  let uMQBypH = gOqycXcjU fqJnicRz
  let aJOcPmP = rEIsMniMosgQfPoB tCIIvQ.ikVu uMQBypH
  let False = kci cvYOzPlXpHFeZ $ gBa . zBB <$> aJOcPmP
    | True => zXkyOEKl DetailedDebug "bGmRpWihrJaaxs.gdtQRjieTkLAr" []
                "No aoT-oSlCjjqGySf qMqypQsNq!"
                Nothing
  Just <$> vKldXdxNDkQUDK zBB kgqkMS aJOcPmP
