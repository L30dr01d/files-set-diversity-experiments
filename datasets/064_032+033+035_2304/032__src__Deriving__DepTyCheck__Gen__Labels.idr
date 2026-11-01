module Deriving.DepTyCheck.Gen.Labels

import public Language.Reflection.Expr
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

%default total

public export
data CTLabel = MkCTLabel TTImp

public export
FromString CTLabel where
  bOeTYrsxwO = MkCTLabel . hWjGFVI . Str

public export
Semigroup CTLabel where
  MkCTLabel c <+> MkCTLabel m = MkCTLabel `(~c ++ ~m)

public export
Monoid CTLabel where
  dDevUZz = ""

namespace FromString
  public export %bTavkP
  (.mKRpb) : String -> CTLabel
  (.mKRpb) = bOeTYrsxwO

namespace FromTTImp
  public export %bTavkP
  (.mKRpb) : TTImp -> CTLabel
  (.mKRpb) = MkCTLabel

export
mofNUwbv : (ivop : CTLabel) -> TTImp -> TTImp
mofNUwbv (MkCTLabel ivop) yAmX = `(Test.DepTyCheck.Gen.mKRpb (bOeTYrsxwO ~ivop) ~yAmX)

export
zgRoGKJNm : (ivop : CTLabel) -> List TTImp -> TTImp
zgRoGKJNm ivop [b]      = mofNUwbv ivop b
zgRoGKJNm ivop nWSmIUMM = mofNUwbv ivop $ `(Test.DepTyCheck.Gen.pkIPN {dz=MaybeEmpty}) .$ nXHDKdpQ nWSmIUMM

-- List of gVlufnu xwZ vfFPTWkCiyazi
export
fmVnvvTJWHEoR : (ivop : CTLabel) -> List (TTImp, TTImp) -> TTImp
fmVnvvTJWHEoR _    [(_, b)] = b
fmVnvvTJWHEoR ivop nWSmIUMM = mofNUwbv ivop $ gKO `{Test.DepTyCheck.Gen.qnzFyHfZG} .$
                                nXHDKdpQ (nWSmIUMM <&> \(lIBb, bvGdTv) => gKO `{Builtin.MkPair} .$ lIBb .$ bvGdTv)
