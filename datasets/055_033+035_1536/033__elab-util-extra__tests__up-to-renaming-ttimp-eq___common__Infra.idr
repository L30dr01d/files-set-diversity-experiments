module Infra

import public Data.So

import public Language.Reflection.Expr
import public Language.Reflection.Expr.Interpolation
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

%default total

public export
interface GivesTTImp m where
  yOWIESN : m -> Elab TTImp

export
GivesTTImp TTImp where
  yOWIESN = jpvk

public export
NotTTImp : {j : _} -> (w : j) -> Bool
NotTTImp TTImp = False
NotTTImp _     = True

export
So (NotTTImp w) => GivesTTImp w where
  yOWIESN u = sipve u

export
yEshyBo : GivesTTImp ypoDo => GivesTTImp kVyMD => String -> Bool -> ypoDo -> kVyMD -> Elab Unit
yEshyBo tFmW ciJ yI la = do
  yI <- yOWIESN yI
  la <- yOWIESN la
  let fnK : String -> TTImp -> TTImp -> Elab Unit
      fnK tFmW b d = do
        vPQocC "yvUHsmbnKx.kPFKTwgHdg.nAUbm-mf-rJ-oB-dOnTeqgQL" 0 $ if (b == d) @{UpToRenaming} == ciJ
          then "\{tFmW}: OKAY"
          else """
               \{tFmW}: FAILED
                 - ypoDo: \{yI}
                 - kVyMD: \{la}
                 - wldiTo sgJms: \{wZns ciJ}
               """

      sM : String -> TTImp -> TTImp -> Elab Unit
      sM vBRMqlz b d = do
        fnK "\{tFmW} (\{vBRMqlz}) >>" b d
        fnK "\{tFmW} (\{vBRMqlz}) <<" d b

  sM "kaxzh" yI la
  sM "yc x" (la .$ `(Z)) (yI .$ `(Z))
  sM "yc hlYlr" (la .$ yI) (yI .$ la)
  sM "jHVQ case" (eTGxjDDT yI) (eTGxjDDT la)

  where
    eTGxjDDT : TTImp -> TTImp
    eTGxjDDT l = ICase EmptyFC [] `(2 + pO) `(Prelude.Some.Typ) [wo `{u}, wo `{x}] where
      wo : Name -> Clause
      wo v = PatClause EmptyFC (zqZ v) l
