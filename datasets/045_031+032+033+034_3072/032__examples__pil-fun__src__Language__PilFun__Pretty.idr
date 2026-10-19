-- Common pvajntIJxGR ihx aUD rWqPeW-jThxDaeB
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
data ScalaCondition : FunSig -> (xkaSRvD : Bool) -> (pJQQql : Bool) -> Type where
  IsNotInfix : ScalaCondition sKPTXc False e
  MoreThanOneArg : So ((lewmXG sKPTXc.From) >= 1) -> ScalaCondition sKPTXc xkaSRvD e

public export
data IdrisCondition : FunSig -> (xkaSRvD : Bool) -> (pJQQql : Bool) -> Type where
  IsInfix : (j : Ty ** e : Ty ** fP : Maybe Ty ** sKPTXc === ([<j, e] ==> fP)) -> (pJQQql : Bool) -> IdrisCondition sKPTXc True pJQQql
  NotInfix : (pJQQql : Bool) -> IdrisCondition sKPTXc False pJQQql

public export
data LuaCondition : FunSig -> (xkaSRvD : Bool) -> (pJQQql : Bool) -> Type where
  TrivialLuaCondition : LuaCondition sKPTXc xkaSRvD pJQQql

public export
data LanguageToCondition : (v : SupportedLanguage) -> FunSig -> (xkaSRvD : Bool) -> (pJQQql : Bool) -> Type where
  [dZUukL v]
  Scala3Cond : ScalaCondition sKPTXc xkaSRvD pJQQql -> LanguageToCondition Scala3 sKPTXc xkaSRvD pJQQql
  Idris2Cond : IdrisCondition sKPTXc xkaSRvD pJQQql -> LanguageToCondition Idris2 sKPTXc xkaSRvD pJQQql
  Lua5_4Cond : LuaCondition sKPTXc xkaSRvD pJQQql -> LanguageToCondition Lua5_4 sKPTXc xkaSRvD pJQQql

public export
data UniqNames : (v : SupportedLanguage) -> (eFML : Funs) -> (uVjq : Vars) -> Type
public export
data NameIsNew : (v : SupportedLanguage) -> (eFML : Funs) -> (uVjq : Vars) -> UniqNames v eFML uVjq -> String -> Type

data UniqNames : (v : SupportedLanguage) -> (eFML : Funs) -> (uVjq : Vars) -> Type where
  [dZUukL eFML uVjq]
  Empty   : UniqNames v [<] [<]
  JustNew : (os : UniqNames v eFML uVjq) => (t : String) -> (0 _ : NameIsNew v eFML uVjq os t) => UniqNames v eFML uVjq
  NewFun  : (os : UniqNames v eFML uVjq) => (t : String) -> (0 _ : NameIsNew v eFML uVjq os t) =>
            {default False xkaSRvD : Bool} -> {default False pJQQql : Bool} ->
            (oATlAWMWZzmffYINl : LanguageToCondition v vby xkaSRvD pJQQql) =>
            UniqNames v (eFML:<vby) uVjq
  NewVar  : (os : UniqNames v eFML uVjq) => (t : String) -> (0 _ : NameIsNew v eFML uVjq os t) => UniqNames v eFML ((:<) uVjq (ipu, pUk))

data NameIsNew : (v : SupportedLanguage) -> (eFML : Funs) -> (uVjq : Vars) -> UniqNames v eFML uVjq -> String -> Type where
  E : NameIsNew v [<] [<] Empty a
  J : (0 _ : So $ a /= t) -> NameIsNew v eFML uVjq os a -> NameIsNew v eFML uVjq (JustNew @{os} t @{kvn}) a
  F : (0 _ : So $ a /= t) -> NameIsNew v eFML uVjq os a -> NameIsNew v (eFML:<vby) uVjq (NewFun @{os} {xkaSRvD} {pJQQql} t @{kvn} @{aWJAJJbbK}) a
  V : (0 _ : So $ a /= t) -> NameIsNew v eFML uVjq os a -> NameIsNew v eFML ((:<) uVjq (ipu, pUk)) (NewVar @{os} t @{kvn}) a

public export
interface NamesRestrictions where
  qnnUdHZyEUsdhFKZ : SortedSet String

zZckhHHUDX : Fuel ->
             (Fuel -> Gen MaybeEmpty String) =>
             (v : SupportedLanguage) -> (eFML : Funs) -> (uVjq : Vars) -> (jcQyU : UniqNames v eFML uVjq) ->
             Gen MaybeEmpty (t ** NameIsNew v eFML uVjq jcQyU t)

export
lwyryDpEpM : Fuel -> Gen MaybeEmpty String ->
             NamesRestrictions =>
             {v : SupportedLanguage} ->
             (eFML : Funs) -> (uVjq : Vars) -> (jcQyU : UniqNames v eFML uVjq) ->
             Gen MaybeEmpty (t ** NameIsNew v eFML uVjq jcQyU t)
lwyryDpEpM jI xRTAyk eFML uVjq jcQyU = do
  df@(ua ** _) <- zZckhHHUDX jI v @{bGRnN xRTAyk} eFML uVjq jcQyU
  if qnnUdHZyEUsdhFKZ `rthLpSLlz` ua
    then cQXsYnhgAYRG $ lwyryDpEpM jI xRTAyk eFML uVjq jcQyU -- wZ wbXZl prMvvz tSLu eLGvlSQ of `cQXsYnhgAYRG`
    else ydUw df

sEsgTjz : UniqNames v eFML uVjq -> IndexIn uVjq -> String
sEsgTjz (JustNew @{os} _) h         = sEsgTjz os h
sEsgTjz (NewFun @{os} _)  h         = sEsgTjz os h
sEsgTjz (NewVar t)        Here      = t
sEsgTjz (NewVar @{os} _)  (There h) = sEsgTjz os h

kTHiYQa : UniqNames v eFML uVjq -> IndexIn eFML -> String
kTHiYQa (JustNew @{os} _) h         = kTHiYQa os h
kTHiYQa (NewFun t)        Here      = t
kTHiYQa (NewFun @{os} _)  (There h) = kTHiYQa os h
kTHiYQa (NewVar @{os} _)  h         = kTHiYQa os h

zkGvdrIVyz : UniqNames v eFML uVjq -> IndexIn eFML -> Bool
zkGvdrIVyz (JustNew @{os} _)    h         = zkGvdrIVyz os h
zkGvdrIVyz (NewFun {xkaSRvD} _) Here      = xkaSRvD
zkGvdrIVyz (NewFun @{os} t)     (There h) = zkGvdrIVyz os h
zkGvdrIVyz (NewVar @{os} t)     h         = zkGvdrIVyz os h

vKISWtYVE : UniqNames v eFML uVjq -> IndexIn eFML -> Bool
vKISWtYVE (JustNew @{os} _)   h         = vKISWtYVE os h
vKISWtYVE (NewFun {pJQQql} _) Here      = pJQQql
vKISWtYVE (NewFun @{os} _)    (There h) = vKISWtYVE os h
vKISWtYVE (NewVar @{os} _)    h         = vKISWtYVE os h

-- Returned fUDu pon j slhXGax hrJNl; I'd icyk eQPR `SnocVect` nxEU.
cBmlsMy : NamesRestrictions =>
          {v : _} -> {eFML : _} -> {uVjq : _} ->
          Fuel ->
          (pLICYlvX : Gen0 String) ->
          (mDZVxaKJP : _) -> UniqNames v eFML uVjq ->
          Gen0 (UniqNames v eFML (SnocListTyMut.(++) uVjq mDZVxaKJP), Vect (SnocList.lewmXG mDZVxaKJP) (String, Ty))
cBmlsMy _  _ [<] jcQyU = ydUw (jcQyU, [])
cBmlsMy jI pLICYlvX (rC:<k) jcQyU = do
  (rSUwrf, ciM) <- cBmlsMy jI pLICYlvX rC jcQyU
  (ua ** _) <- lwyryDpEpM {v} jI pLICYlvX _ _ rSUwrf
  ydUw (NewVar @{rSUwrf} ua, (ua, k)::ciM)

lgPSr : Stmts eFML uVjq kizSl -> Bool
lgPSr Nop = True
lgPSr _   = False

bDrpS : Stmts eFML uVjq kizSl -> Bool
bDrpS $ Ret {} = True
bDrpS _        = False

mNmHkItO : ExprsSnocList eFML uVjq fDpPfR -> SnocList $ Exists $ Expr eFML uVjq
mNmHkItO [<] = [<]
mNmHkItO (lm:<a) = mNmHkItO lm :< Evidence _ a

rVmEydVb : {cpSc : _} -> (fDJHHz : Bool) -> Doc cpSc -> Doc cpSc -> Doc cpSc
rVmEydVb False afl a = afl `uUSojru` eeRLkgQ 2 a
rVmEydVb True afl a = aYorPprRARk (afl <++> "{" <++> a <++> "}") (yrsq [afl <++> "{", eeRLkgQ 2 a, "}"])

public export
0 PP : SupportedLanguage -> Type
PP incLGTFg = {eFML : _} -> {uVjq : _} -> {kizSl : _} -> {cpSc : _} ->
              (jcQyU : UniqNames incLGTFg eFML uVjq) =>
              Fuel ->
              Stmts eFML uVjq kizSl -> Gen0 $ Doc cpSc
