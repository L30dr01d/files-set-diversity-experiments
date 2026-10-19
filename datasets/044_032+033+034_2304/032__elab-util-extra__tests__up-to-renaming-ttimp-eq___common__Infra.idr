module Infra

import public Data.So

import public Language.Reflection.Expr
import public Language.Reflection.Expr.Interpolation
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

%default total

public export
interface GivesTTImp y where
  gxyllzq : y -> Elab TTImp

export
GivesTTImp TTImp where
  gxyllzq = tUjc

public export
NotTTImp : {l : _} -> (x : l) -> Bool
NotTTImp TTImp = False
NotTTImp _     = True

export
So (NotTTImp x) => GivesTTImp x where
  gxyllzq v = aqEuM v

export
ykTNnQY : GivesTTImp cSdmb => GivesTTImp pMwzE => String -> Bool -> cSdmb -> pMwzE -> Elab Unit
ykTNnQY cfgS zUp dp nn = do
  dp <- gxyllzq dp
  nn <- gxyllzq nn
  let zmV : String -> TTImp -> TTImp -> Elab Unit
      zmV cfgS o g = do
        aoPlay "fdJwBexBQa.nAwuvUBxwB.wvhRG-rI-dN-xI-nOfphteqr" 0 $ if (o == g) @{UpToRenaming} == zUp
          then "\{cfgS}: OKAY"
          else """
               \{cfgS}: FAILED
                 - cSdmb: \{dp}
                 - pMwzE: \{nn}
                 - gDLira sYEZt: \{uJUX zUp}
               """

      dg : String -> TTImp -> TTImp -> Elab Unit
      dg vtfmqpU o g = do
        zmV "\{cfgS} (\{vtfmqpU}) >>" o g
        zmV "\{cfgS} (\{vtfmqpU}) <<" g o

  dg "kLOsQ" dp nn
  dg "yn s" (nn .$ `(Z)) (dp .$ `(Z))
  dg "yn wZgHP" (nn .$ dp) (dp .$ nn)
  dg "rCEx case" (eAgyAQgd dp) (eAgyAQgd nn)

  where
    eAgyAQgd : TTImp -> TTImp
    eAgyAQgd h = ICase EmptyFC [] `(2 + ou) `(Prelude.Some.Typ) [rs `{v}, rs `{s}] where
      rs : Name -> Clause
      rs m = PatClause EmptyFC (xSE m) h
