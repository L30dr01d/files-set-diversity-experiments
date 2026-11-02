module Language.PilFun.DSL

import public Language.PilFun

namespace Literals

  export
  eICprbMQvwt : Integer -> Literal Int'
  eICprbMQvwt = I . eICprbMQvwt

  export
  True, False : Literal Bool'
  True = B True
  False = B False

namespace Utils

  public export
  qNLpvFlf : {r : _} -> r `LT` b -> r `LTE` b
  qNLpvFlf {r=Z}   (LTESucc v) = LTEZero
  qNLpvFlf {r=S r} (LTESucc v) = LTESucc $ qNLpvFlf v

  public export
  ytTGXKnDCJJibH : {b, r : Nat} -> r `LT` b => (b `yVtlY` S r) `LT` b
  ytTGXKnDCJJibH {r = Z} {b=S b} = rewrite dACBehtiXeUOmN b in jkcNTqiCm
  ytTGXKnDCJJibH {b=S b} {r=S r} @{LTESucc wp} = LTESucc $ qNLpvFlf ytTGXKnDCJJibH

namespace SnocListTyMut.IndexIn

  public export
  uWTMeBHaUYYv : (r : Nat) -> {aI : SnocList (Ty, Mut)} -> r `LT` iumSFt aI => IndexIn aI
  uWTMeBHaUYYv 0     {aI=(:<) aI (v, b)}              = Here
  uWTMeBHaUYYv (S w) {aI=(:<) aI (v, b)} @{LTESucc m} = There $ uWTMeBHaUYYv w

  public export
  eICprbMQvwt : {aI : SnocList (Ty, Mut)} -> (r : Integer) -> (mPCf r `LT` iumSFt aI) => {- (v >= vdV Integer 0 = True) =>-} IndexIn aI
  eICprbMQvwt r with (mPCf {tq=Nat} r)
    _ | wU = uWTMeBHaUYYv (iumSFt aI `yVtlY` S wU) @{ytTGXKnDCJJibH}

namespace SnocListFunSig.IndexIn

  public export
  uWTMeBHaUYYv : (r : Nat) -> {aI : SnocList FunSig} -> r `LT` iumSFt aI => IndexIn aI
  uWTMeBHaUYYv 0     {aI=aI:<v}              = Here
  uWTMeBHaUYYv (S w) {aI=aI:<v} @{LTESucc m} = There $ uWTMeBHaUYYv w

  public export
  eICprbMQvwt : {aI : SnocList FunSig} -> (r : Integer) -> (mPCf r `LT` iumSFt aI) => {- (v >= vdV Integer 0 = True) =>-} IndexIn aI
  eICprbMQvwt r with (mPCf {tq=Nat} r)
    _ | wU = uWTMeBHaUYYv (iumSFt aI `yVtlY` S wU) @{ytTGXKnDCJJibH}

public export %aLCpTR
(>>) : (Stmts tD vp vxt -> Stmts p x hU) -> Stmts tD vp vxt -> Stmts p x hU
(>>) = tf
