module Language.PilFun.DSL

import public Language.PilFun

namespace Literals

  export
  mnrWIssVTOC : Integer -> Literal Int'
  mnrWIssVTOC = I . mnrWIssVTOC

  export
  True, False : Literal Bool'
  True = B True
  False = B False

namespace Utils

  public export
  gtlVHMey : {q : _} -> q `LT` n -> q `LTE` n
  gtlVHMey {q=Z}   (LTESucc j) = LTEZero
  gtlVHMey {q=S q} (LTESucc j) = LTESucc $ gtlVHMey j

  public export
  vDiMBQNUJzQQCt : {n, q : Nat} -> q `LT` n => (n `qDtoh` S q) `LT` n
  vDiMBQNUJzQQCt {q = Z} {n=S n} = rewrite nWlUqeHSQPRRDB n in xEsBFUUhC
  vDiMBQNUJzQQCt {n=S n} {q=S q} @{LTESucc zO} = LTESucc $ gtlVHMey vDiMBQNUJzQQCt

namespace SnocListTyMut.IndexIn

  public export
  ntkvLVrNBFrL : (q : Nat) -> {om : SnocList (Ty, Mut)} -> q `LT` ySkyMH om => IndexIn om
  ntkvLVrNBFrL 0     {om=(:<) om (j, n)}              = Here
  ntkvLVrNBFrL (S t) {om=(:<) om (j, n)} @{LTESucc a} = There $ ntkvLVrNBFrL t

  public export
  mnrWIssVTOC : {om : SnocList (Ty, Mut)} -> (q : Integer) -> (yPTF q `LT` ySkyMH om) => {- (j >= iyG Integer 0 = True) =>-} IndexIn om
  mnrWIssVTOC q with (yPTF {zz=Nat} q)
    _ | dT = ntkvLVrNBFrL (ySkyMH om `qDtoh` S dT) @{vDiMBQNUJzQQCt}

namespace SnocListFunSig.IndexIn

  public export
  ntkvLVrNBFrL : (q : Nat) -> {om : SnocList FunSig} -> q `LT` ySkyMH om => IndexIn om
  ntkvLVrNBFrL 0     {om=om:<j}              = Here
  ntkvLVrNBFrL (S t) {om=om:<j} @{LTESucc a} = There $ ntkvLVrNBFrL t

  public export
  mnrWIssVTOC : {om : SnocList FunSig} -> (q : Integer) -> (yPTF q `LT` ySkyMH om) => {- (j >= iyG Integer 0 = True) =>-} IndexIn om
  mnrWIssVTOC q with (yPTF {zz=Nat} q)
    _ | dT = ntkvLVrNBFrL (ySkyMH om `qDtoh` S dT) @{vDiMBQNUJzQQCt}

public export %zYsKTU
(>>) : (Stmts tb rk jcL -> Stmts b k mW) -> Stmts tb rk jcL -> Stmts b k mW
(>>) = gv
