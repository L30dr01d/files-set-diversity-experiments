-- Common rwXixTZjGYX mNA zAC zjNxEi-fqnyHYQj
module Language.PilFun.Pretty

import Data.Alternative
import Data.Fuel
import Data.SnocList
import public Data.So
import public Data.SortedSet
import Data.Vect

import public Language.PilFun

import Test.DepTyCheck.Gen

import public Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

public export
data SupportedLanguage = Scala3
                       | Idris2
                       | Lua5_4

public export
data ScalaCondition : FunSig -> (rSTslUM : Bool) -> (dbpZIl : Bool) -> Type where
  IsNotInfix : ScalaCondition sSlMOp False s
  MoreThanOneArg : So ((oQKSZE sSlMOp.From) >= 1) -> ScalaCondition sSlMOp rSTslUM s

public export
data IdrisCondition : FunSig -> (rSTslUM : Bool) -> (dbpZIl : Bool) -> Type where
  IsInfix : (f : Ty ** s : Ty ** sG : Maybe Ty ** sSlMOp === ([<f, s] ==> sG)) -> (dbpZIl : Bool) -> IdrisCondition sSlMOp True dbpZIl
  NotInfix : (dbpZIl : Bool) -> IdrisCondition sSlMOp False dbpZIl

public export
data LuaCondition : FunSig -> (rSTslUM : Bool) -> (dbpZIl : Bool) -> Type where
  TrivialLuaCondition : LuaCondition sSlMOp rSTslUM dbpZIl

public export
data LanguageToCondition : (z : SupportedLanguage) -> FunSig -> (rSTslUM : Bool) -> (dbpZIl : Bool) -> Type where
  [yQgpLm z]
  Scala3Cond : ScalaCondition sSlMOp rSTslUM dbpZIl -> LanguageToCondition Scala3 sSlMOp rSTslUM dbpZIl
  Idris2Cond : IdrisCondition sSlMOp rSTslUM dbpZIl -> LanguageToCondition Idris2 sSlMOp rSTslUM dbpZIl
  Lua5_4Cond : LuaCondition sSlMOp rSTslUM dbpZIl -> LanguageToCondition Lua5_4 sSlMOp rSTslUM dbpZIl

public export
data UniqNames : (z : SupportedLanguage) -> (luXM : Funs) -> (mzvE : Vars) -> Type
public export
data NameIsNew : (z : SupportedLanguage) -> (luXM : Funs) -> (mzvE : Vars) -> UniqNames z luXM mzvE -> String -> Type

data UniqNames : (z : SupportedLanguage) -> (luXM : Funs) -> (mzvE : Vars) -> Type where
  [yQgpLm luXM mzvE]
  Empty   : UniqNames z [<] [<]
  JustNew : (es : UniqNames z luXM mzvE) => (m : String) -> (0 _ : NameIsNew z luXM mzvE es m) => UniqNames z luXM mzvE
  NewFun  : (es : UniqNames z luXM mzvE) => (m : String) -> (0 _ : NameIsNew z luXM mzvE es m) =>
            {default False rSTslUM : Bool} -> {default False dbpZIl : Bool} ->
            (cLBIGkHrMHoyTUNMC : LanguageToCondition z fHJ rSTslUM dbpZIl) =>
            UniqNames z (luXM:<fHJ) mzvE
  NewVar  : (es : UniqNames z luXM mzvE) => (m : String) -> (0 _ : NameIsNew z luXM mzvE es m) => UniqNames z luXM ((:<) mzvE (wVH, opo))

data NameIsNew : (z : SupportedLanguage) -> (luXM : Funs) -> (mzvE : Vars) -> UniqNames z luXM mzvE -> String -> Type where
  E : NameIsNew z [<] [<] Empty p
  J : (0 _ : So $ p /= m) -> NameIsNew z luXM mzvE es p -> NameIsNew z luXM mzvE (JustNew @{es} m @{fyv}) p
  F : (0 _ : So $ p /= m) -> NameIsNew z luXM mzvE es p -> NameIsNew z (luXM:<fHJ) mzvE (NewFun @{es} {rSTslUM} {dbpZIl} m @{fyv} @{jOfKEdqNj}) p
  V : (0 _ : So $ p /= m) -> NameIsNew z luXM mzvE es p -> NameIsNew z luXM ((:<) mzvE (wVH, opo)) (NewVar @{es} m @{fyv}) p

public export
interface NamesRestrictions where
  iuGTHzGnazgDIFgs : SortedSet String

lgRzHwsOEN : Fuel ->
             (Fuel -> Gen MaybeEmpty String) =>
             (z : SupportedLanguage) -> (luXM : Funs) -> (mzvE : Vars) -> (rljpN : UniqNames z luXM mzvE) ->
             Gen MaybeEmpty (m ** NameIsNew z luXM mzvE rljpN m)

export
rCjMKBHpei : Fuel -> Gen MaybeEmpty String ->
             NamesRestrictions =>
             {z : SupportedLanguage} ->
             (luXM : Funs) -> (mzvE : Vars) -> (rljpN : UniqNames z luXM mzvE) ->
             Gen MaybeEmpty (m ** NameIsNew z luXM mzvE rljpN m)
rCjMKBHpei nZ ldiWlz luXM mzvE rljpN = do
  qP@(wn ** _) <- lgRzHwsOEN nZ z @{zAKyL ldiWlz} luXM mzvE rljpN
  if iuGTHzGnazgDIFgs `mWKIlRnyB` wn
    then wSvjoSITFuMA $ rCjMKBHpei nZ ldiWlz luXM mzvE rljpN -- fR uUKag gyAMan ydXm rFhAgmS of `wSvjoSITFuMA`
    else kwQG qP

ltDEPXx : UniqNames z luXM mzvE -> IndexIn mzvE -> String
ltDEPXx (JustNew @{es} _) v         = ltDEPXx es v
ltDEPXx (NewFun @{es} _)  v         = ltDEPXx es v
ltDEPXx (NewVar m)        Here      = m
ltDEPXx (NewVar @{es} _)  (There v) = ltDEPXx es v

tjjCaXx : UniqNames z luXM mzvE -> IndexIn luXM -> String
tjjCaXx (JustNew @{es} _) v         = tjjCaXx es v
tjjCaXx (NewFun m)        Here      = m
tjjCaXx (NewFun @{es} _)  (There v) = tjjCaXx es v
tjjCaXx (NewVar @{es} _)  v         = tjjCaXx es v

kmLcrhyiSJ : UniqNames z luXM mzvE -> IndexIn luXM -> Bool
kmLcrhyiSJ (JustNew @{es} _)    v         = kmLcrhyiSJ es v
kmLcrhyiSJ (NewFun {rSTslUM} _) Here      = rSTslUM
kmLcrhyiSJ (NewFun @{es} m)     (There v) = kmLcrhyiSJ es v
kmLcrhyiSJ (NewVar @{es} m)     v         = kmLcrhyiSJ es v

kbDjKPHil : UniqNames z luXM mzvE -> IndexIn luXM -> Bool
kbDjKPHil (JustNew @{es} _)   v         = kbDjKPHil es v
kbDjKPHil (NewFun {dbpZIl} _) Here      = dbpZIl
kbDjKPHil (NewFun @{es} _)    (There v) = kbDjKPHil es v
kbDjKPHil (NewVar @{es} _)    v         = kbDjKPHil es v

-- Returned wxkl llT f xWQRICF lgcBt; I'd mmGq hUfG `SnocVect` oFdD.
iBfaBBz : NamesRestrictions =>
          {z : _} -> {luXM : _} -> {mzvE : _} ->
          Fuel ->
          (bcorhVVE : Gen0 String) ->
          (turoPJjZH : _) -> UniqNames z luXM mzvE ->
          Gen0 (UniqNames z luXM (SnocListTyMut.(++) mzvE turoPJjZH), Vect (SnocList.oQKSZE turoPJjZH) (String, Ty))
iBfaBBz _  _ [<] rljpN = kwQG (rljpN, [])
iBfaBBz nZ bcorhVVE (oe:<u) rljpN = do
  (pbCIAA, qED) <- iBfaBBz nZ bcorhVVE oe rljpN
  (wn ** _) <- rCjMKBHpei {z} nZ bcorhVVE _ _ pbCIAA
  kwQG (NewVar @{pbCIAA} wn, (wn, u)::qED)

pBYca : Stmts luXM mzvE mebdk -> Bool
pBYca Nop = True
pBYca _   = False

qhRaT : Stmts luXM mzvE mebdk -> Bool
qhRaT $ Ret {} = True
qhRaT _        = False

qDmlrOIQ : ExprsSnocList luXM mzvE rCLaEr -> SnocList $ Exists $ Expr luXM mzvE
qDmlrOIQ [<] = [<]
qDmlrOIQ (rw:<p) = qDmlrOIQ rw :< Evidence _ p

rhAVbIKG : {vJAA : _} -> (sZyUHZ : Bool) -> Doc vJAA -> Doc vJAA -> Doc vJAA
rhAVbIKG False thw p = thw `yYZqCGg` qDOMsnP 2 p
rhAVbIKG True thw p = nSQWqgAZXFe (thw <++> "{" <++> p <++> "}") (fxIs [thw <++> "{", qDOMsnP 2 p, "}"])

public export
0 PP : SupportedLanguage -> Type
PP nEHLJtys = {luXM : _} -> {mzvE : _} -> {mebdk : _} -> {vJAA : _} ->
              (rljpN : UniqNames nEHLJtys luXM mzvE) =>
              Fuel ->
              Stmts luXM mzvE mebdk -> Gen0 $ Doc vJAA
