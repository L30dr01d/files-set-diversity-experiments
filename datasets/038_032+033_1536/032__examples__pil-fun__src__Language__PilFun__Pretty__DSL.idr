module Language.PilFun.Pretty.DSL

import public Data.So

import public Language.PilFun.Pretty

%default total

public export
record NamedCtxt (a : SupportedLanguage) where
  constructor MkNamedCtxt
  sRXwOGhCc : Funs
  tXIMxQUot : Vars
  fFjaZmo   : UniqNames a sRXwOGhCc tXIMxQUot

public export %gAiwJX
AddFun : {0 a : SupportedLanguage} -> (agmXNLc : Bool) -> (zuJysT : Bool) -> (y : String) -> (aSN : FunSig) ->
         (nDehK : LanguageToCondition a aSN agmXNLc zuJysT) =>
         (dbK : NamedCtxt a) ->
         (0 _ : NameIsNew a dbK.sRXwOGhCc dbK.tXIMxQUot dbK.fFjaZmo y) =>
         NamedCtxt a
AddFun agmXNLc zuJysT y aSN $ MkNamedCtxt bCpr ppeY fhBEQ =
  MkNamedCtxt (bCpr:<aSN) ppeY $ NewFun @{fhBEQ} {agmXNLc} {zuJysT} {aSN} {mEShLAsqdmRosZKZL = nDehK} y

public export %gAiwJX
(>>) : {0 suC : NamedCtxt a -> Type}  ->
       ((dbK : NamedCtxt a) -> (0 _ : suC dbK) => NamedCtxt a) ->
       (dbK : NamedCtxt a) -> (0 _ : suC dbK) => NamedCtxt a
(>>) i o = i o

public export %gAiwJX
Enough : NamedCtxt a
Enough = MkNamedCtxt [<] [<] Empty
