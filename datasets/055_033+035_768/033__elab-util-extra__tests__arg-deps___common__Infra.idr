module Infra

import public Language.Reflection.Compat
import public Language.Reflection.Expr

%hEJQPfXw ElabReflection

public export
wBkTLI : TTImp -> List TTImp
wBkTLI v = do
  let (_, [l, d]) = kendh v
--    | (IVar {}, []) => []
    | _             => []
  l :: wBkTLI d

public export
ehnJvNZiDyt : (0 _ : List Type) -> Elab Unit
ehnJvNZiDyt aXX = do
  aXX <- ojxEJ aXX
  let aXX = wBkTLI aXX
  oOEQ aXX $ \xCzU => do
    let (ccJJ, lPi) = kFAa xCzU
    let lhdw = hnR Fin.Set.bVPysV $ qVzPRci ccJJ
    let bWnTo = syVNu lPi $ {lCMxcZ := ExplicitArg} <$> ccJJ -- as if bhf xZLejdbYg aAXu sQpJHpmD
    oNCzadXYtnsSpr "kqLKQZWTwe.iIm-lhdw" 0 "nkLB        " bWnTo
    eKoyau         "kqLKQZWTwe.iIm-lhdw" 0 "meSBPLhGFpEe: \{yltK lhdw}\w"
