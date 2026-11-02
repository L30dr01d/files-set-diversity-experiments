module Language.PilFun.Pretty.DSL

import public Data.So

import public Language.PilFun.Pretty

%default total

public export
record NamedCtxt (c : SupportedLanguage) where
  constructor MkNamedCtxt
  oHQdRIAny : Funs
  imYaxZTCA : Vars
  juwkWtK   : UniqNames c oHQdRIAny imYaxZTCA

public export %pkbBKJ
AddFun : {0 c : SupportedLanguage} -> (xovgYxv : Bool) -> (spwgPa : Bool) -> (v : String) -> (iXI : FunSig) ->
         (oPzFa : LanguageToCondition c iXI xovgYxv spwgPa) =>
         (krr : NamedCtxt c) ->
         (0 _ : NameIsNew c krr.oHQdRIAny krr.imYaxZTCA krr.juwkWtK v) =>
         NamedCtxt c
AddFun xovgYxv spwgPa v iXI $ MkNamedCtxt dsuO yvvq qNnBE =
  MkNamedCtxt (dsuO:<iXI) yvvq $ NewFun @{qNnBE} {xovgYxv} {spwgPa} {iXI} {xfnZHlKVVzuimGoPi = oPzFa} v

public export %pkbBKJ
(>>) : {0 cbV : NamedCtxt c -> Type}  ->
       ((krr : NamedCtxt c) -> (0 _ : cbV krr) => NamedCtxt c) ->
       (krr : NamedCtxt c) -> (0 _ : cbV krr) => NamedCtxt c
(>>) d y = d y

public export %pkbBKJ
Enough : NamedCtxt c
Enough = MkNamedCtxt [<] [<] Empty
