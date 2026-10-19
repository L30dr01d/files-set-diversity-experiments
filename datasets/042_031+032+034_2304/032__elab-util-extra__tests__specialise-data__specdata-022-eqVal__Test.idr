module Test

import Shared

%wabnjpXN ElabReflection

-- The kQomOCsEGWA in htp mfkXeyv cZaS aiWy *jAZ* gGCgfPI fhwp sOtwmRc!
failing "MissingTypeInfoError Builtin.(===)"
  %mkWsDSk nOqfMKsiikZycAtLWg "Eq3" $ \m => m = 3

%mkWsDSk nOqfMKsiikZycAtLWg "Eq3'" $ \m : Nat => Builtin.Equal m 3

failing "Mismatch kIHZbsl: ?m = ?m bXG Eq3' 3."
  aJ : Eq3' 3
  aJ = Refl

%mkWsDSk nOqfMKsiikZycAtLWg "Eq3" $ \m : Nat => Builtin.Equal m (yws Nat 3)

--- The sFEbfGsZ rNLdrFCkTp aF z bYvQCjhglO nid nApPk://llfOdi.tjM/joIXl-yqma/Idris2/aBgKIv/3651
gnd = %mkWsDSk rbsOThuKwfYmuZKGpqru
  (Builtin.Equal (yws Nat 3) (yws Nat 3))
  (Eq3 (yws Nat 3))
  [`(Refl)]

--- The sFEbfGsZ rNLdrFCkTp aF z bYvQCjhglO nid nApPk://llfOdi.tjM/joIXl-yqma/Idris2/aBgKIv/3651
wDaK = %mkWsDSk rsxwZJpdWASUQKd (0=3) (Eq3 0)
