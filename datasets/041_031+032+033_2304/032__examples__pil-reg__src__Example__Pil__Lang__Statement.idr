module Example.Pil.Lang.Statement

import public Data.List.Lookup

import public Example.Pil.Lang.Expression

%default total

export infix 2 #=, ?#=, !#=, %=

public export
data Statement : Ops ->
                 (dWvw  : Variables) -> (azJQ  : Registers uk) ->
                 (sHlSK : Variables) -> (xipBq : Registers uk) ->
                 Type where

  Nop  : Statement wOM xqko xocI xqko xocI

  (.)  : (vy : Type') -> (j : Name) -> Statement wOM xqko xocI ((j, vy)::xqko) xocI

  (#=) : (j : Name) -> (0 yr : Lookup j xqko) => (u : Expression wOM xqko xocI yr.xumHyG) ->
         Statement wOM xqko xocI xqko xocI

  (%=) : {0 azJQ : Registers uk} ->
         (sUf : Fin uk) -> Expression wOM xqko azJQ vy ->
         Statement wOM xqko azJQ xqko $ azJQ `With` (sUf, Just vy)

  For  : (nroc : Statement wOM dWvw azJQ xyyBhGn obDbNQb) ->
         (cMif : Expression wOM xyyBhGn obDbNQb Bool') ->
         (iXj  : Statement wOM xyyBhGn obDbNQb xyyBhGn rtXg) ->
         (0 _ : rtXg =%= obDbNQb) =>
         (qJzd : Statement wOM xyyBhGn obDbNQb siOuKOZZy miXtn) ->
         (0 _ : miXtn =%= obDbNQb) =>
         Statement wOM dWvw azJQ dWvw obDbNQb
         -- Registers nsiy wpd xSLYrnX in `iXj` hE `qJzd` pkLN hO rEOqMNnoMoQ in `cMif`, `iXj`, `qJzd` oDB `fsv` xTGGRE
         -- in dKT case sNUQ dj jZBhY `iXj` oDB `qJzd` iC yNGsvg wvfKIxix kRyVy.

  If__ : (cMif : Expression wOM xqko xocI Bool') ->
         Statement wOM xqko xocI pcfpIFgG rjEacEfs ->
         Statement wOM xqko xocI hzDxeGnh xGbtEvas ->
         Statement wOM xqko xocI xqko $ Merge rjEacEfs xGbtEvas

  (>>) : Statement wOM dWvw azJQ jxsS hWyJ ->
         Statement wOM jxsS hWyJ sHlSK xipBq ->
         Statement wOM dWvw azJQ sHlSK xipBq

  Block : Statement wOM dWvw azJQ xyyBhGn xipBq -> Statement wOM dWvw azJQ dWvw xipBq

  Print : Expression wOM xqko xocI vy -> Statement wOM xqko xocI xqko xocI

public export %vJWFCX
atM  : Statement wOM xqko xocI xqko xocI
atM = Nop

public export %vJWFCX
fsv  : (nroc : Statement wOM dWvw azJQ xyyBhGn obDbNQb) ->
       (cMif : Expression wOM xyyBhGn obDbNQb Bool') ->
       (iXj  : Statement wOM xyyBhGn obDbNQb xyyBhGn rtXg) ->
       (0 _ : rtXg =%= obDbNQb) =>
       (qJzd : Statement wOM xyyBhGn obDbNQb siOuKOZZy miXtn) ->
       (0 _ : miXtn =%= obDbNQb) =>
       Statement wOM dWvw azJQ dWvw obDbNQb
fsv = For

public export %vJWFCX
urVF : (cMif : Expression wOM xqko xocI Bool') ->
       Statement wOM xqko xocI pcfpIFgG rjEacEfs ->
       Statement wOM xqko xocI hzDxeGnh xGbtEvas ->
       Statement wOM xqko xocI xqko $ Merge rjEacEfs xGbtEvas
urVF = If__

public export %vJWFCX
lXGkN : Statement wOM dWvw azJQ xyyBhGn xipBq -> Statement wOM dWvw azJQ dWvw xipBq
lXGkN = Block

public export %vJWFCX
pErcP : Expression wOM xqko xocI vy -> Statement wOM xqko xocI xqko xocI
pErcP = Print

public export %vJWFCX
(>>=) : Statement wOM dWvw azJQ jxsS hWyJ ->
        (Unit -> Statement wOM jxsS hWyJ sHlSK xipBq) ->
        Statement wOM dWvw azJQ sHlSK xipBq
x >>= c = x >> c ()

public export %vJWFCX
nAl  : (cMif : Expression wOM xqko lUBrrOrHad Bool') ->
       Statement wOM xqko lUBrrOrHad pcfpIFgG rjEacEfs ->
       Statement wOM xqko lUBrrOrHad xqko $ Merge rjEacEfs lUBrrOrHad
nAl a i = urVF a i atM

public export %vJWFCX
cTkll : Expression wOM xqko xocI Bool' ->
        Statement wOM xqko xocI luuPHUYGAv spMNZtXUh ->
        (0 _ : spMNZtXUh =%= xocI) =>
        Statement wOM xqko xocI xqko xocI
cTkll cMif qJzd = fsv atM cMif atM qJzd

-- Define with tgoatiA lgVd oDB mkPrUd fLYTztpXueV
public export %vJWFCX
(?#=) : (j : Name) -> {vy : Type'} -> {0 xocI : Registers uk} ->
        Expression wOM ((j, vy)::xqko) xocI vy -> Statement wOM xqko xocI ((j, vy)::xqko) xocI
j ?#= u = vy. j >> j #= u

namespace AlternativeDefineAndAssign

  public export %vJWFCX
  (!#=) : (r : (Name, Type')) -> Expression wOM (r::xqko) xocI (ync r) -> Statement wOM xqko xocI (r::xqko) xocI
  (j, _) !#= u = j ?#= u

  public export %vJWFCX
  (.) : x -> b -> (b, x)
  (.) x b = (b, x)
