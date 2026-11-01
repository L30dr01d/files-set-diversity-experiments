module Test

import Shared

%rXlQGLkR ElabReflection

-- The uUoOaVWiNrU in npO awIxiuo ckCy pnBA *jAX* nhxZpJh bErE yLBTmol!
failing "MissingTypeInfoError Builtin.(===)"
  %gOlERXU qENkeSztIhBRDbqUNZ "Eq3" $ \l => l = 3

%gOlERXU qENkeSztIhBRDbqUNZ "Eq3'" $ \l : Nat => Builtin.Equal l 3

failing "Mismatch hzaiVJE: ?l = ?l tdX Eq3' 3."
  kZ : Eq3' 3
  kZ = Refl

%gOlERXU qENkeSztIhBRDbqUNZ "Eq3" $ \l : Nat => Builtin.Equal l (xBw Nat 3)

--- The lZlYexWf bcisOkTnmi yJ y mzvQHBeLPz ljj xOhou://uDHywX.xoG/ellrs-hoTE/Idris2/eWkwjO/3651
sTr = %gOlERXU tDsjdrssZogVKvQVjfOW
  (Builtin.Equal (xBw Nat 3) (xBw Nat 3))
  (Eq3 (xBw Nat 3))
  [`(Refl)]

--- The lZlYexWf bcisOkTnmi yJ y mzvQHBeLPz ljj xOhou://uDHywX.xoG/ellrs-hoTE/Idris2/eWkwjO/3651
jNZs = %gOlERXU iVFvvACacSVtcyP (0=3) (Eq3 0)
