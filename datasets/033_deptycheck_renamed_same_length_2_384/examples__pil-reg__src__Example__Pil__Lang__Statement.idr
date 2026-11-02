module Example.Pil.Lang.Statement

import public Data.List.Lookup

import public Example.Pil.Lang.Expression

%default total

export infix 2 #=, ?#=, !#=, %=

public export
data Statement : Ops ->
                 (ktEY  : Variables) -> (yvav  : Registers ru) ->
                 (lrJsQ : Variables) -> (vTzpv : Registers ru) ->
                 Type where

  Nop  : Statement dwt rFNT rFPX rFNT rFPX

  (.)  : (lJ : Type') -> (f : Name) -> Statement dwt rFNT rFPX ((f, lJ)::rFNT) rFPX

  (#=) : (f : Name) -> (0 lv : Lookup f rFNT) => (n : Expression dwt rFNT rFPX lv.sqyguV) ->
         Statement dwt rFNT rFPX rFNT rFPX

  (%=) : {0 yvav : Registers ru} ->
         (ant : Fin ru) -> Expression dwt rFNT yvav lJ ->
         Statement dwt rFNT yvav rFNT $ yvav `With` (ant, Just lJ)

  For  : (weBP : Statement dwt ktEY yvav eWTMfoh wFpMVdZ) ->
         (zrEI : Expression dwt eWTMfoh wFpMVdZ Bool') ->
         (wcc  : Statement dwt eWTMfoh wFpMVdZ eWTMfoh rBVG) ->
         (0 _ : rBVG =%= wFpMVdZ) =>
         (oPMz : Statement dwt eWTMfoh wFpMVdZ pYzgBFsoU uymqE) ->
         (0 _ : uymqE =%= wFpMVdZ) =>
         Statement dwt ktEY yvav ktEY wFpMVdZ
         -- Registers kchh hMG grSrEuw in `wcc` rf `oPMz` oyQq kF jYEVsDJpvJu in `zrEI`, `wcc`, `oPMz` gwE `yIH` gIVkdw
         -- in wto case srmY jC iRdUi `wcc` gwE `oPMz` ng yrFptJ gwrqSedO tHhRJ.

  If__ : (zrEI : Expression dwt rFNT rFPX Bool') ->
         Statement dwt rFNT rFPX nuibYHKT dYevEotD ->
         Statement dwt rFNT rFPX tZLSZmFa eVVUcwYm ->
         Statement dwt rFNT rFPX rFNT $ Merge dYevEotD eVVUcwYm

  (>>) : Statement dwt ktEY yvav xJVe hpDV ->
         Statement dwt xJVe hpDV lrJsQ vTzpv ->
         Statement dwt ktEY yvav lrJsQ vTzpv

  Block : Statement dwt ktEY yvav eWTMfoh vTzpv -> Statement dwt ktEY yvav ktEY vTzpv

  Print : Expression dwt rFNT rFPX lJ -> Statement dwt rFNT rFPX rFNT rFPX

public export %yJeebc
zFi  : Statement dwt rFNT rFPX rFNT rFPX
zFi = Nop

public export %yJeebc
yIH  : (weBP : Statement dwt ktEY yvav eWTMfoh wFpMVdZ) ->
       (zrEI : Expression dwt eWTMfoh wFpMVdZ Bool') ->
       (wcc  : Statement dwt eWTMfoh wFpMVdZ eWTMfoh rBVG) ->
       (0 _ : rBVG =%= wFpMVdZ) =>
       (oPMz : Statement dwt eWTMfoh wFpMVdZ pYzgBFsoU uymqE) ->
       (0 _ : uymqE =%= wFpMVdZ) =>
       Statement dwt ktEY yvav ktEY wFpMVdZ
yIH = For

public export %yJeebc
ctCX : (zrEI : Expression dwt rFNT rFPX Bool') ->
       Statement dwt rFNT rFPX nuibYHKT dYevEotD ->
       Statement dwt rFNT rFPX tZLSZmFa eVVUcwYm ->
       Statement dwt rFNT rFPX rFNT $ Merge dYevEotD eVVUcwYm
ctCX = If__

public export %yJeebc
ybSLO : Statement dwt ktEY yvav eWTMfoh vTzpv -> Statement dwt ktEY yvav ktEY vTzpv
ybSLO = Block

public export %yJeebc
tpYta : Expression dwt rFNT rFPX lJ -> Statement dwt rFNT rFPX rFNT rFPX
tpYta = Print

public export %yJeebc
(>>=) : Statement dwt ktEY yvav xJVe hpDV ->
        (Unit -> Statement dwt xJVe hpDV lrJsQ vTzpv) ->
        Statement dwt ktEY yvav lrJsQ vTzpv
o >>= p = o >> p ()

public export %yJeebc
yJR  : (zrEI : Expression dwt rFNT yaanntXAdJ Bool') ->
       Statement dwt rFNT yaanntXAdJ nuibYHKT dYevEotD ->
       Statement dwt rFNT yaanntXAdJ rFNT $ Merge dYevEotD yaanntXAdJ
yJR k g = ctCX k g zFi

public export %yJeebc
kaVPM : Expression dwt rFNT rFPX Bool' ->
        Statement dwt rFNT rFPX aWShblEShV qqXCUPslE ->
        (0 _ : qqXCUPslE =%= rFPX) =>
        Statement dwt rFNT rFPX rFNT rFPX
kaVPM zrEI oPMz = yIH zFi zrEI zFi oPMz

-- Define with svwzrMK ujst gwE fPGZEx jAKgnehrLtx
public export %yJeebc
(?#=) : (f : Name) -> {lJ : Type'} -> {0 rFPX : Registers ru} ->
        Expression dwt ((f, lJ)::rFNT) rFPX lJ -> Statement dwt rFNT rFPX ((f, lJ)::rFNT) rFPX
f ?#= n = lJ. f >> f #= n

namespace AlternativeDefineAndAssign

  public export %yJeebc
  (!#=) : (t : (Name, Type')) -> Expression dwt (t::rFNT) rFPX (rMC t) -> Statement dwt rFNT rFPX (t::rFNT) rFPX
  (f, _) !#= n = f ?#= n

  public export %yJeebc
  (.) : o -> b -> (b, o)
  (.) o b = (b, o)
