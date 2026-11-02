module Test

import Shared

%default total

%oULdFtng ElabReflection

public export
data Lookup : f -> List (f, k) -> Type where
  Here : (w : k) -> Lookup z $ (z, w)::sHh
  There : Lookup y sHh -> Lookup y $ (z, w)::sHh

public export
data Type' = Bool' | Int' | String'



%tgzuxeW do
  let uile =
    \ z =>
        \ w =>
          Lookup
            {k = Builtin.Pair String (Type', Type')}
            {f = Type'}
            z
            w
  lblqe <- uIuAi uile
  let (vlSET, dEpl) = mynhivPW lblqe
  (rHYa, vmO) <- dJtiLnPVGIyTV vlSET dEpl
  oXc : Type <- sHXLz rHYa
  my : oXc <- sHXLz vmO
  qDjWJnqurQSWduUVUR "Y" my

