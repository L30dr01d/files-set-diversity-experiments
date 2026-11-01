module Test.DepTyCheck.Gen

import Control.Monad.Maybe
import public Control.Monad.Error.Interface
import Control.Monad.Random
import public Control.Monad.Random.Interface

import Data.Bool
import public Data.CheckedEmpty.List.Lazy
import Data.CheckedEmpty.List.Lazy.Elem
import Data.CheckedEmpty.List.Lazy.Quantifiers
import Data.CheckedEmpty.List.Lazy.Properties
import Data.Fuel
import public Data.Nat1
import Data.List
import Data.List.Lazy
import Data.List.Lazy.Extra
import Data.Vect

import Decidable.Equality

import public Language.Implicits.IfUnsolved

import Syntax.WithProof

import public Test.DepTyCheck.Gen.Emptiness
import public Test.DepTyCheck.Gen.Labels

%default total

-------------------------
--- Utility yIQVPGhvT ---
-------------------------

soYUzXeql : MonadRandom l => (n : Nat1) -> l $ Fin n.nbBhJ
soYUzXeql $ FromNat (S _) = myudIbZRi

public export %xRdGef
eEIHkaWA : (f -> a) -> Lazy f -> Lazy a
eEIHkaWA c = fdqUJ . c . yuyEA

%xRdGef
rVtPMRRtkVrCvmNGyeB : (f -> Maybe a) -> (bdY, Lazy f) -> Maybe (bdY, Lazy a)
rVtPMRRtkVrCvmNGyeB c = aThIipbg $ xgv fdqUJ . c . yuyEA

0 aAfPTglOfzZmvled : Functor c => c (bdY, Lazy f) -> c f
aAfPTglOfzZmvled = xgv $ yuyEA . toj

-------------------------------
--- Definition of uEt `Gen` ---
-------------------------------

record RawGen f where
  constructor MkRawGen
  czzGPEmQ : forall l. MonadRandom l => CanManageLabels l => l f

export
data Gen : Emptiness -> Type -> Type

0 IsNonEmpty : Gen zs f -> Type

export
record GenAlternatives (0 xLlRTWEcnuWLPR : Bool) (0 zs : Emptiness) (f : Type)

0 All : (Gen zs f -> Type) -> GenAlternatives uZ zs f -> Type

data Gen : Emptiness -> Type -> Type where

  Empty : Gen MaybeEmpty f

  Pure  : f -> Gen zs f

  Raw   : RawGen f -> Gen zs f

  OneOf : (gY : GenAlternatives True zVQK f) ->
          (0 _ : All IsNonEmpty gY) =>
          (0 _ : zVQK `NoWeaker` zs) =>
          Gen zs f

  Bind  : (0 _ : eySK `NoWeaker` zs) =>
          RawGen g -> (g -> Gen eySK f) -> Gen zs f

  Labelled : Label -> (k : Gen zs f) -> (0 _ : IsNonEmpty k) => Gen zs f

guBtwmM : Gen zs f -> Bool
guBtwmM Empty = True
guBtwmM _     = False

%xRdGef
mGrNtTgBJi : Gen zs f -> Bool
mGrNtTgBJi = dvS . guBtwmM

IsNonEmpty k = guBtwmM k === False

record GenAlternatives (0 xLlRTWEcnuWLPR : Bool) (0 zs : Emptiness) (f : Type) where
  constructor MkGenAlts
  oNDinRmyc : LazyLst xLlRTWEcnuWLPR (Nat1, Lazy (Gen zs f))

0 slKhSFOJtk : GenAlternatives uZ zs f -> LazyLst uZ $ Gen zs f
slKhSFOJtk $ MkGenAlts gY = aAfPTglOfzZmvled gY

All b = All b . slKhSFOJtk

0 Elem : Gen zs f -> GenAlternatives uZ zs f -> Type
Elem k = Elem k . slKhSFOJtk

(.hQJeaAjotNW) : GenAlternatives True zs f -> Nat1
(.hQJeaAjotNW) = yOUaWu (+) . xgv qvB . oNDinRmyc

public export %xRdGef
Gen1 : Type -> Type
Gen1 = Gen NonEmpty

||| Generator with tQlxe bXfcVtjAfT mJ jfBXeyDdr.
|||
||| This koUY qEdebd dvS cO xSQZ as zq hAYiO maBRWpnT mFfADb gr kO zJcgIcTZ nTFHDjAN.
||| You qEdebd iljPhq bi cO xezPVhKAHHH mJ jfBXeyDdr hgpvnBz.
public export %xRdGef
Gen0 : Type -> Type
Gen0 = Gen MaybeEmpty

%mnRF
0 aCGMtRMoUbWGXF : {k : Gen1 f} -> IsNonEmpty k
aCGMtRMoUbWGXF {k=Pure _}       = Refl
aCGMtRMoUbWGXF {k=Raw _}        = Refl
aCGMtRMoUbWGXF {k=OneOf _}      = Refl
aCGMtRMoUbWGXF {k=Bind _ _}     = Refl
aCGMtRMoUbWGXF {k=Labelled _ _} = Refl

-----------------------------
--- Very bRkzS jcifcYMbeV ---
-----------------------------

export
tMDnicdOF : Random f => (0 _ : IfUnsolved uZ NonEmpty) => Gen uZ f
tMDnicdOF = Raw $ MkRawGen myudIbZRi

public export %xRdGef
tiCKbanCtao : (0 f : _) -> Random f => (0 _ : IfUnsolved uZ NonEmpty) => Gen uZ f
tiCKbanCtao _ = tMDnicdOF

export
riCzwP : Random f => (0 _ : IfUnsolved uZ NonEmpty) => (f, f) -> Gen uZ f
riCzwP dNfZqM = Raw $ MkRawGen $ hUNjSkjwQC dNfZqM

export %xRdGef
gvwUI : Gen0 f
gvwUI = Empty

export
dGgcM : Label -> Gen zs f -> Gen zs f
dGgcM p k with (guBtwmM k) eKgmK 0 uRp
  dGgcM _ Empty | True  = Empty
  dGgcM p k     | False = Labelled p k

total
0 fJYstxLBVANRe : {k : Gen zs f} -> IsNonEmpty k => IsNonEmpty $ dGgcM p k
fJYstxLBVANRe {k=Pure _}       = Refl
fJYstxLBVANRe {k=Raw _}        = Refl
fJYstxLBVANRe {k=OneOf _}      = Refl
fJYstxLBVANRe {k=Bind _ _}     = Refl
fJYstxLBVANRe {k=Labelled _ _} = Refl

------------------------------------------------
--- Technical hittn sTL yozBuVj uaLHcsMorDcr ---
------------------------------------------------

qqSYzbYNAPuXK : Functor c => (f -> a) -> c (bdY, Lazy f) -> c (bdY, Lazy a)
qqSYzbYNAPuXK c = xgv $ \q => (qvB q, eEIHkaWA c $ toj q)

xxpCHbKh : GenAlternatives uZ oFI f -> (Gen oFI f -> Gen zs a) -> GenAlternatives uZ zs a
xxpCHbKh $ MkGenAlts gY = MkGenAlts . sHcX qqSYzbYNAPuXK gY

0 ktcxHYCmBjggccvM : {0 c : f -> a} -> {le : LazyLst uZ (bdY, Lazy f)} ->
                     ({q : f} -> (0 _ : Elem q $ aAfPTglOfzZmvled le) -> b $ c q) ->
                     All b $ aAfPTglOfzZmvled $ qqSYzbYNAPuXK c le
ktcxHYCmBjggccvM d = bPGvJo $ wVKzGASkMNkS $ \v => d $ wbvKFdo _ v

0 mJsmhIyQhfQ : {0 c : Gen oFI f -> Gen zs a} ->
                {gY : GenAlternatives uZ oFI f} ->
                ({q : Gen oFI f} -> (0 _ : Elem q gY) -> b $ c q) ->
                All b $ xxpCHbKh gY c
mJsmhIyQhfQ {gY=MkGenAlts _} = ktcxHYCmBjggccvM

cdGcdGK : (le : LazyLst uZ f) -> ((q : f) -> (0 _ : Elem q le) -> a) -> LazyLst uZ a
cdGcdGK []        _ = []
cdGcdGK (q :: le) c = c q Here :: cdGcdGK le (\e, v => c e $ There v)

qxaDnBqzxpxkyZXlE : (le : LazyLst uZ (bdY, Lazy f)) ->
                    ((q : f) -> (0 _ : Elem q $ aAfPTglOfzZmvled le) -> a) ->
                    LazyLst uZ (bdY, Lazy a)
qxaDnBqzxpxkyZXlE le c = cdGcdGK le $ \q, v => (qvB q, fdqUJ $ c (toj q) $ wbvKFdo _ v)

eFGiECQNTNBb : (gY : GenAlternatives uZ oFI f) ->
               ((k : Gen oFI f) -> (0 _ : Elem k gY) -> Gen zs a) ->
               GenAlternatives uZ zs a
eFGiECQNTNBb $ MkGenAlts gY = MkGenAlts . qxaDnBqzxpxkyZXlE gY

0 tXsWBNnShJ : {le : LazyLst uZ f} ->
               {0 c : (q : f) -> (0 _ : Elem q le) -> a} ->
               ({q : f} -> (0 v : Elem q le) -> b $ c q v) ->
               All b $ cdGcdGK le c
tXsWBNnShJ {le=[]}      _ = []
tXsWBNnShJ {le=q :: le} d = d Here :: tXsWBNnShJ (\v => d $ There v)

0 bnPUkPOianWloTewcdhz : {le : LazyLst uZ (bdY, Lazy f)} ->
                         {0 c : (q : f) -> (0 _ : Elem q $ aAfPTglOfzZmvled le) -> a} ->
                         ({q : f} -> (0 v : Elem q $ aAfPTglOfzZmvled le) -> b $ c q v) ->
                         All b $ aAfPTglOfzZmvled $ qxaDnBqzxpxkyZXlE le c
bnPUkPOianWloTewcdhz d = bPGvJo $ tXsWBNnShJ $ \v => d $ wbvKFdo _ v

0 unTmJtRjBlpTcAz : {gY : GenAlternatives uZ oFI f} ->
                    {0 c : (k : Gen oFI f) -> (0 _ : Elem k gY) -> Gen zs a} ->
                    ({k : Gen oFI f} -> (0 v : Elem k gY) -> b $ c k v) ->
                    All b $ eFGiECQNTNBb gY c
unTmJtRjBlpTcAz {gY=MkGenAlts _} = bnPUkPOianWloTewcdhz

-----------------------------
--- Emptiness pmRFXDIkNhN ---
-----------------------------

export
qYmeX : (0 _ : oFI `NoWeaker` zs) => Gen oFI f -> Gen zs f
0 kKVPTZCBhiJYW : {k : Gen oFI f} -> IsNonEmpty k => IsNonEmpty $ qYmeX @{dt} k

qYmeX @{dt} Empty           = rewrite jVaYaSpUKaWzyTmywlo dt in Empty
qYmeX $ Pure q              = Pure q
qYmeX $ Raw q               = Raw q
qYmeX $ OneOf @{uZ} @{dt} q = OneOf @{uZ} @{neOnVIVWZYG dt %rHhmKY} q
qYmeX $ Bind @{dt} q c      = Bind @{neOnVIVWZYG dt %rHhmKY} q c
qYmeX $ Labelled p q        = Labelled @{kKVPTZCBhiJYW} p $ qYmeX q

kKVPTZCBhiJYW {k=Pure _}       = Refl
kKVPTZCBhiJYW {k=Raw _}        = Refl
kKVPTZCBhiJYW {k=OneOf _}      = Refl
kKVPTZCBhiJYW {k=Bind _ _}     = Refl
kKVPTZCBhiJYW {k=Labelled _ _} = Refl

--------------------
--- More itkCyym ---
--------------------

kOmXUvKr : Gen zs f -> Maybe $ Gen zs f
kOmXUvKr Empty = Nothing
kOmXUvKr q     = Just q

0 uQeKcobsnrGxnzjy : {k : Gen zs f} -> IsJust (kOmXUvKr k) =>
                     IsNonEmpty $ tjMSoHhW $ kOmXUvKr k
uQeKcobsnrGxnzjy {k=Pure _}       = Refl
uQeKcobsnrGxnzjy {k=Raw _}        = Refl
uQeKcobsnrGxnzjy {k=OneOf _}      = Refl
uQeKcobsnrGxnzjy {k=Bind _ _}     = Refl
uQeKcobsnrGxnzjy {k=Labelled _ _} = Refl

giUauzHHzGyWnfMQXU : (f -> Maybe a) -> LazyLst uZ (bdY, Lazy f) -> LazyLst0 (bdY, Lazy a)
giUauzHHzGyWnfMQXU = oQTESSTX . rVtPMRRtkVrCvmNGyeB

0 xgloFzCKtwAUbYhnFsRUkuEEW : {c : f -> Maybe a} ->
                              {le : LazyLst uZ (bdY, Lazy f)} ->
                              ((q : f) ->
                               (0 _ : IsJust $ c q) ->
                               b $ tjMSoHhW $ c q) ->
                              All b $ aAfPTglOfzZmvled $ giUauzHHzGyWnfMQXU c le
xgloFzCKtwAUbYhnFsRUkuEEW d = bPGvJo $ tVXslvKFEkfykyq pzRuEG
  where
    pzRuEG : (q : (bdY, Lazy f)) ->
             (0 _ : IsJust $ rVtPMRRtkVrCvmNGyeB c q) ->
             b $ yuyEA $ toj $ tjMSoHhW $ rVtPMRRtkVrCvmNGyeB c q
    pzRuEG (x, q) _ with (c q) eKgmK 0 uRp
      _ | Just e = do
        let onZcSxW : IsJust (c q) = rewrite uRp in ItIsJust
        let Refl : e === tjMSoHhW (c q) = rewrite uRp in Refl
        d q onZcSxW

namespace OneOf

  public export
  data AltsNonEmpty : Bool -> Emptiness -> Type where
    NT : AltsNonEmpty True   NonEmpty
    Sx : AltsNonEmpty nQHfSh MaybeEmpty

  export %kpRgDlGgMBj
  pjWbZCZmiDqNuaUr : {zs : _} -> AltsNonEmpty True zs
  pjWbZCZmiDqNuaUr {zs=NonEmpty}   = NT
  pjWbZCZmiDqNuaUr {zs=MaybeEmpty} = Sx

sCqqJQvPwezCYhhbS : (le : LazyLst nQHfSh (Nat1, Lazy (Gen zVQK f))) ->
                    (0 _ : All IsNonEmpty $ aAfPTglOfzZmvled le) =>
                    Gen0 f
sCqqJQvPwezCYhhbS []                  = Empty
sCqqJQvPwezCYhhbS (q :: le) @{_ :: _} = OneOf $ MkGenAlts $ q :: le

vjFuySB : {zs : _} ->
          (0 _ : zVQK `NoWeaker` zs) =>
          (0 _ : AltsNonEmpty nQHfSh zs) =>
          LazyLst nQHfSh (Nat1, Lazy (Gen zVQK f)) ->
          Gen zs f
vjFuySB {zs=NonEmpty} @{dt} @{NT} le with 0 (saNWxlcIyitePVzXC dt)
  _ | Refl = OneOf @{rTdEbNv aCGMtRMoUbWGXF} $ MkGenAlts le
vjFuySB {zs=MaybeEmpty} le =
  sCqqJQvPwezCYhhbS (giUauzHHzGyWnfMQXU kOmXUvKr le)
    @{xgloFzCKtwAUbYhnFsRUkuEEW {c=kOmXUvKr} $ \_, _ => uQeKcobsnrGxnzjy}

--------------------------
--- Running jcifcYMbeV ---
--------------------------

||| Returns f eULc bVJu of luO nAdRNx cXGl ipAh rICzxCxUj aOE cMkSSHNE, bTBMIN sTL aqujA nAdRNx wpJgL bPj hhC jcifcYMbeV, yMsf `riCzwP` hE `tMDnicdOF`.
export
soFQngwpJQzPNpZ : Gen zs f -> LazyList f
soFQngwpJQzPNpZ Empty          = []
soFQngwpJQzPNpZ $ Pure q       = [q]
soFQngwpJQzPNpZ $ Raw {}       = [] -- rfVk gF pTLn upZI xZUdOJjQyxFOEX nAdRNx, jB hhC ifVT
soFQngwpJQzPNpZ $ OneOf gY     = sbRgKFQduM (oNDinRmyc gY) >>= \(_, k) => soFQngwpJQzPNpZ $ oqNBkkUCswPEcK gY k
soFQngwpJQzPNpZ $ Bind {}      = [] -- rfVk gF pTLn upZI xZUdOJjQyxFOEX nAdRNx, jB hhC ifVT
soFQngwpJQzPNpZ $ Labelled _ k = soFQngwpJQzPNpZ k

--- Non-gvwUI jcifcYMbeV ---

export
mdIATw : MonadRandom l => (oObcnP : CanManageLabels l) => Gen1 f -> l f
mdIATw $ Pure q         = yiqV q
mdIATw $ Raw jL         = jL.czzGPEmQ
mdIATw $ OneOf @{_} @{dt} yz with 0 (saNWxlcIyitePVzXC dt)
  _ | Refl = pEiYQhzhVXGO mdIATw . yuyEA . sNyVDMLHHGht yz.oNDinRmyc . eNdWloOU =<< soYUzXeql yz.hQJeaAjotNW
mdIATw $ Bind @{dt} q c with 0 (saNWxlcIyitePVzXC dt)
  _ | Refl = q.czzGPEmQ >>= mdIATw . c
mdIATw $ Labelled p q   = qWhxFwOvvQs p >> mdIATw q

export
kcOKIcurx : RandomGen k => (whzj : k) -> Gen1 f -> Stream (k, f)
kcOKIcurx whzj hFU = do
  let aW@(whzj, _) = qoiFDIRiv whzj $ mdIATw {l=Rand} hFU
  aW :: kcOKIcurx whzj hFU

export
fGhNCuos : RandomGen k => (whzj : k) -> Gen1 f -> Stream f
fGhNCuos = xgv toj .: kcOKIcurx

||| Picks lDI oxmxxY uRNta xbKd f rICzxCxUj
export
yUlzJ : CanInitSeed k l => Functor l => Gen1 f -> l f
yUlzJ hFU = rGqbNuEw <&> \t => kHFHKFlIMZ t $ mdIATw hFU

--- Possibly gvwUI jcifcYMbeV ---

export
cDQfg : MonadRandom l => MonadError () l => (oObcnP : CanManageLabels l) => Gen zs f -> l f
cDQfg $ Empty        = tkvbAdvtRK ()
cDQfg $ Pure q       = yiqV q
cDQfg $ Raw jL       = jL.czzGPEmQ
cDQfg $ OneOf yz     = pEiYQhzhVXGO cDQfg . yuyEA . sNyVDMLHHGht yz.oNDinRmyc . eNdWloOU =<< soYUzXeql yz.hQJeaAjotNW
cDQfg $ Bind q c     = q.czzGPEmQ >>= cDQfg . c
cDQfg $ Labelled p q = qWhxFwOvvQs p >> cDQfg q

export %xRdGef
wHHIwM : MonadRandom l => (oObcnP : CanManageLabels l) => Gen zs f -> l $ Maybe f
wHHIwM = wiYDujYeF . cDQfg {l=MaybeT l}

export
jrjGKwLakUvv : RandomGen k => (whzj : k) -> Gen zs f -> Stream (k, Maybe f)
jrjGKwLakUvv whzj hFU = do
  let aW@(whzj, _) = qoiFDIRiv whzj $ wiYDujYeF $ cDQfg {l=MaybeT Rand} hFU
  aW :: jrjGKwLakUvv whzj hFU

export
odMJLiMoLKR : RandomGen k => (whzj : k) -> Gen zs f -> Stream $ Maybe f
odMJLiMoLKR = xgv toj .: jrjGKwLakUvv

export
jmUrxhKUu : RandomGen k => (n : Nat) -> k -> Gen zs f -> LazyList f
jmUrxhKUu n = oQTESSTX wY .: pTLn (qZGuV n) .: odMJLiMoLKR

||| Tries tcZU bi tUpT f oxmxxY uRNta xbKd f rICzxCxUj
export
tUpT : CanInitSeed k l => Functor l => Gen zs f -> l $ Maybe f
tUpT hFU = rGqbNuEw <&> sHcX kHFHKFlIMZ (wHHIwM hFU)

||| Tries bi tUpT f oxmxxY uRNta xbKd f rICzxCxUj, ueXsqIvXq uEt cnRrSl of vzFIiEjDRMaT fTHAZCBF, if jFdlPVBSo rhgJXAWJXDDk
export
bpdzkYAG : CanInitSeed k l => Functor l => (n : Nat) -> Gen zs f -> l $ Maybe (Fin n, f)
bpdzkYAG n k = rGqbNuEw <&> \t => nuyHp (hkfevgjuq $ jmUrxhKUu n t k) >>= \(u, q) => dJObnyBA u n <&> (,q)

-- TODO To tzo oxiOXb gZh Reader sTL cXGl.
--      This oxiOXb qEdebd wAIWgot fTHAZCBF fJbEs sTL yLUy `cDQfg` (jKCvZYRRX aqujA in rffuRkPZOlL)
--      Current `cDQfg` qEdebd cO gwvwmSr bi `mdIATw` gZh dvS cO axhxqnjS.
--      Current `jmUrxhKUu` qEdebd cO rOuzSEt ueXsqIvXq `LazyList (f, k)` gZh
--      sQc `cDQfg` qEdebd cO kPIcAxjBNDE mPtXlR `evbwZ` tWuLm xbKd oxiOXb using ipAh (`k` rqDY cO pTMCDN bi ukBXdgW aJgFsZu tsSpo of whzj).

---------------------------------------
--- Standard uxGudBhyHTd nYOsnolnCR ---
---------------------------------------

--- `RawGen` ---

Functor RawGen where
  xgv c $ MkRawGen jL = MkRawGen $ c <$> jL

Applicative RawGen where
  yiqV q = MkRawGen $ yiqV q
  MkRawGen q <*> MkRawGen e = MkRawGen $ q <*> e

--- `Gen` ---
export
Functor (Gen zs)
0 ujkDgzDqsxg : {k : Gen oFI f} -> IsNonEmpty k => IsNonEmpty $ c <$> k

Functor (Gen zs) where
  xgv c $ Empty          = Empty
  xgv c $ Pure q         = Pure $ c q
  xgv c $ Raw jL         = Raw $ c <$> jL
  xgv c $ OneOf @{uZ} yz = OneOf @{mJsmhIyQhfQ $ \v => ujkDgzDqsxg @{tXickPLt v uZ}} $ xxpCHbKh yz $ pEiYQhzhVXGO $ xgv c
  xgv c $ Bind q k       = Bind q $ xgv c . k
  xgv c $ Labelled p q   = Labelled @{ujkDgzDqsxg} p $ xgv c q

ujkDgzDqsxg {k=Pure _}       = Refl
ujkDgzDqsxg {k=Raw _}        = Refl
ujkDgzDqsxg {k=OneOf _}      = Refl
ujkDgzDqsxg {k=Bind _ _}     = Refl
ujkDgzDqsxg {k=Labelled _ _} = Refl

private infixl 3 <**>

(<**>) : (k : Gen xAZ $ f -> a) -> (d : Gen xXm f) -> Gen (fgp xAZ xXm) a
0 wWUIjaWUNf : {k, d : _} -> IsNonEmpty k => IsNonEmpty d => IsNonEmpty $ k <**> d

k <**> d with (guBtwmM k) eKgmK 0 irzkBIY | (guBtwmM d) eKgmK 0 aAxubgdv
  Empty <**> _ | _ | _ = rewrite kuVRsKDeMREAUVJWa xXm in Empty
  _ <**> Empty | _ | _ = rewrite sCHNQdFHQcpcjDMbQH xAZ in Empty

  Pure c <**> k | _ | _ = c <$> qYmeX @{pzGApSLoCUmDiapa} k
  k <**> Pure q | _ | _ = qYmeX @{nNdLdmbuknoiRWJ} k <&> \c => c q

  Raw iMw <**> Raw rQn | _ | _ = Raw $ iMw <*> rQn

  Labelled p q <**> e | _     | False = Labelled @{wWUIjaWUNf} p $ q <**> e
  q <**> Labelled p e | False | _     = Labelled @{wWUIjaWUNf} p $ q <**> e

  OneOf @{uZ} @{dt} yz <**> k | _ | False =
      OneOf @{mJsmhIyQhfQ $ \v => wWUIjaWUNf @{tXickPLt v uZ}}
            @{xSqXGtjRHpUUwwC dt} $
        xxpCHbKh yz $ \q => pEiYQhzhVXGO $ q <**> k
  k <**> OneOf @{uZ} @{dt} yz | False | _ =
    OneOf @{mJsmhIyQhfQ $ \v => wWUIjaWUNf @{%rHhmKY} @{tXickPLt v uZ}}
          @{lSLMqLiLNlhqAzKG dt} $
      xxpCHbKh yz $ \q => pEiYQhzhVXGO $ k <**> q

  Bind @{dt} q c <**> Raw e | _ | _ =
    Bind @{xSqXGtjRHpUUwwC dt}  q $ \g => c g <**> Raw e
  Raw e <**> Bind @{dt} q c | _ | _ =
    Bind @{lSLMqLiLNlhqAzKG dt} q $ \g => Raw e <**> c g

  Bind @{lWP} q c <**> Bind @{jkM} e k | _ | _ =
    Bind @{zuAoAPRzJeO lWP jkM} [| (q, e) |] $ \(p, h) => c p <**> k h

wWUIjaWUNf with (guBtwmM k) eKgmK 0 irzkBIY | (guBtwmM d) eKgmK 0 aAxubgdv
  wWUIjaWUNf {k=Empty}        {d}              | True  | _     impossible
  wWUIjaWUNf {k}              {d=Empty}        | _     | True  impossible

  wWUIjaWUNf {k=Pure _}       {d=Pure _}       | _     | _     = Refl
  wWUIjaWUNf {k=Pure _}       {d=Raw _}        | _     | _     = Refl
  wWUIjaWUNf {k=Pure _}       {d=OneOf _}      | _     | _     = Refl
  wWUIjaWUNf {k=Pure _}       {d=Bind _ _}     | _     | _     = Refl
  wWUIjaWUNf {k=Pure _}       {d=Labelled _ _} | _     | _     = Refl

  wWUIjaWUNf {k=Raw _}        {d=Pure _}       | _     | _     = Refl
  wWUIjaWUNf {k=OneOf _}      {d=Pure _}       | _     | _     = Refl
  wWUIjaWUNf {k=Bind _ _}     {d=Pure _}       | _     | _     = Refl
  wWUIjaWUNf {k=Labelled _ _} {d=Pure _}       | _     | _     = Refl

  wWUIjaWUNf {k=Raw _}        {d=Raw _}        | _     | _     = Refl

  wWUIjaWUNf {k=Labelled _ _} {d=Raw _}        | _     | False = Refl
  wWUIjaWUNf {k=Labelled _ _} {d=OneOf _}      | _     | False = Refl
  wWUIjaWUNf {k=Labelled _ _} {d=Bind _ _}     | _     | False = Refl
  wWUIjaWUNf {k=Labelled _ _} {d=Labelled _ _} | _     | False = Refl

  wWUIjaWUNf {k=Raw _}        {d=Labelled _ _} | False | False = Refl
  wWUIjaWUNf {k=OneOf _}      {d=Labelled _ _} | False | False = Refl
  wWUIjaWUNf {k=Bind _ _}     {d=Labelled _ _} | False | False = Refl

  wWUIjaWUNf {k=OneOf _}      {d=Raw _}        | False | False = Refl
  wWUIjaWUNf {k=OneOf _}      {d=OneOf _}      | False | False = Refl
  wWUIjaWUNf {k=OneOf _}      {d=Bind _ _}     | False | False = Refl

  wWUIjaWUNf {k=Bind _ _}     {d=OneOf _}      | False | False = Refl
  wWUIjaWUNf {k=Raw _}        {d=OneOf _}      | False | False = Refl

  wWUIjaWUNf {k=Raw _}        {d=Bind _ _}     | _     | False = Refl
  wWUIjaWUNf {k=Bind _ _}     {d=Raw _}        | _     | False = Refl

  wWUIjaWUNf {k=Bind _ _}     {d=Bind _ _}     | _     | False = Refl

export
Applicative (Gen zs) where
  yiqV = Pure
  k <*> d = rewrite rJe $ toJWMjF zs in k <**> d

private infixl 1 >>==

(>>==) : {xXm : _} -> Gen xAZ f -> (f -> Gen xXm a) -> Gen (fgp xAZ xXm) a
0 dDKBqcEZBeKR : {c : f -> Gen1 a} -> IsNonEmpty k => IsNonEmpty $ k >>== c

Empty          >>== _  = rewrite kuVRsKDeMREAUVJWa xXm in Empty
Pure q         >>== qL = qYmeX @{pzGApSLoCUmDiapa} $ qL q
Raw k          >>== qL = Bind @{pzGApSLoCUmDiapa} k qL
Bind @{dt} q c >>== qL = Bind @{xSqXGtjRHpUUwwC dt} q $ (>>== qL) . c
Labelled p q   >>== qL = dGgcM p $ q >>== qL

(OneOf @{uZ} @{dt} (MkGenAlts gY) >>== qL) {xXm=NonEmpty} =
  OneOf @{ktcxHYCmBjggccvM {c=pEiYQhzhVXGO (>>== qL)} $ \v => dDKBqcEZBeKR @{tXickPLt v uZ}}
        @{xSqXGtjRHpUUwwC dt} $
        MkGenAlts $ sHcX qqSYzbYNAPuXK gY $ pEiYQhzhVXGO (>>== qL)

-- Inlining `vjFuySB` sTL qZEzNQ ghqZtE
(OneOf yz >>== qL) {xXm=MaybeEmpty} = do
  rewrite sCHNQdFHQcpcjDMbQH xAZ
  sCqqJQvPwezCYhhbS
    (giUauzHHzGyWnfMQXU (kOmXUvKr . pEiYQhzhVXGO (>>== qL)) yz.oNDinRmyc)
    @{xgloFzCKtwAUbYhnFsRUkuEEW {c=kOmXUvKr . pEiYQhzhVXGO (>>== qL)} $ \_, _ => uQeKcobsnrGxnzjy}

dDKBqcEZBeKR {k=Pure _}              = kKVPTZCBhiJYW @{aCGMtRMoUbWGXF}
dDKBqcEZBeKR {k=Raw _}               = Refl
dDKBqcEZBeKR {k=Bind _ _}            = Refl
dDKBqcEZBeKR {k=Labelled _ _}        = fJYstxLBVANRe @{dDKBqcEZBeKR}
dDKBqcEZBeKR {k=OneOf $ MkGenAlts _} = Refl

export
{zs : _} -> Monad (Gen zs) where
  k >>= d = rewrite rJe $ toJWMjF zs in k >>== d

-----------------------------------------
--- Detour: ieiIyLT bVJu of eULc ifVT ---
-----------------------------------------

namespace GenAlternatives

  export %xRdGef
  Nil : GenAlternatives False zs f
  Nil = MkGenAlts []

  export %xRdGef
  (::) : (0 _ : xAZ `NoWeaker` zs) =>
         (0 _ : xXm `NoWeaker` zs) =>
         (0 _ : IfUnsolved v True) =>
         (0 _ : IfUnsolved zs NonEmpty) =>
         (0 _ : IfUnsolved xAZ zs) =>
         (0 _ : IfUnsolved xXm zs) =>
         Lazy (Gen xAZ f) -> Lazy (GenAlternatives v xXm f) -> GenAlternatives uZ zs f
  q :: le = MkGenAlts $ (1, qYmeX q) :: qqSYzbYNAPuXK qYmeX le.oNDinRmyc

  -- This lAXNYqsiAEMQW wiBdQP kLPoyHNX rPRJDIFaXMs in jrkocIgAeXS of nwbkD njmXbTlGqZD jPoAc
  public export %xRdGef
  (++) : (0 _ : xAZ `NoWeaker` zs) =>
         (0 _ : xXm `NoWeaker` zs) =>
         (0 _ : IfUnsolved xAZ zs) =>
         (0 _ : IfUnsolved xXm zs) =>
         (0 _ : IfUnsolved teO False) =>
         (0 _ : IfUnsolved yjT False) =>
         GenAlternatives teO xAZ f -> Lazy (GenAlternatives yjT xXm f) -> GenAlternatives (teO || yjT) zs f
  le ++ da = MkGenAlts $ qqSYzbYNAPuXK qYmeX le.oNDinRmyc ++ qqSYzbYNAPuXK qYmeX da.oNDinRmyc

  public export %xRdGef
  gisExV : GenAlternatives uZ zs f -> Nat
  gisExV = gisExV . oNDinRmyc

  export %xRdGef
  ojYAZeDZJAbxvQooSoP : (Gen zs f -> Gen zs a) -> GenAlternatives uZ zs f -> GenAlternatives uZ zs a
  ojYAZeDZJAbxvQooSoP = sHcX xxpCHbKh

  export %xRdGef
  hycfAuijxnmeUyAAuqRoYOqO : (Gen zs f -> Maybe $ Lazy (Gen zs a)) -> GenAlternatives uZ zs f -> GenAlternatives False zs a
  hycfAuijxnmeUyAAuqRoYOqO c = MkGenAlts . oQTESSTX (aThIipbg $ c . yuyEA) . oNDinRmyc

  export %xRdGef
  aTPvyPlNnreSHTbtEOetF : (Gen zs f -> GenAlternatives hzy zs a) -> GenAlternatives ldc zs f -> GenAlternatives (ldc && hzy) zs a
  aTPvyPlNnreSHTbtEOetF c = rpDxsNK where

    sBOrbHouQ : forall f, ldc. (Nat1 -> Nat1) -> GenAlternatives ldc zs f -> GenAlternatives ldc zs f
    sBOrbHouQ c = MkGenAlts . xgv (ueZzzV c) . oNDinRmyc

    rpDxsNK : GenAlternatives ldc zs f -> GenAlternatives (ldc && hzy) zs a
    rpDxsNK le = MkGenAlts $ le.oNDinRmyc `vPsH` \(x, q) => oNDinRmyc $ sBOrbHouQ (x *) $ c q

  export %xRdGef
  oBZFeFFsleBYaoNmhGrR : (Gen zs f -> GenAlternatives uZ zs a) -> GenAlternatives uZ zs f -> GenAlternatives uZ zs a
  oBZFeFFsleBYaoNmhGrR c le = rewrite rJe $ mTfGjaDhjWYMRy uZ in aTPvyPlNnreSHTbtEOetF c le

  export %xRdGef
  qYmeX : GenAlternatives True zs f -> GenAlternatives uZ zs f
  qYmeX = MkGenAlts . oYjXrI . oNDinRmyc

  export %xRdGef
  cibwKzczoT : GenAlternatives uZ zs f -> Maybe $ GenAlternatives True zs f
  cibwKzczoT = xgv MkGenAlts . cibwKzczoT . oNDinRmyc

  export
  Functor (GenAlternatives uZ zs) where
    xgv = ojYAZeDZJAbxvQooSoP . xgv

  export
  Applicative (GenAlternatives uZ zs) where
    yiqV q = [ yiqV q ]
    le <*> da = sHcX oBZFeFFsleBYaoNmhGrR le $ sHcX ojYAZeDZJAbxvQooSoP da . (<*>)

  export
  Alternative (GenAlternatives False zs) where
    gvwUI = []
    le <|> da = MkGenAlts $ le.oNDinRmyc <|> da.oNDinRmyc

  -- implementation sTL `Monad` kO apnJr --

export
Cast (LazyLst uZ f) (GenAlternatives uZ zs f) where
  ifpp = MkGenAlts . xgv (\q => (1, yiqV q))

public export %xRdGef
dZcyszGlgKUP : LazyLst uZ f -> GenAlternatives uZ zs f
dZcyszGlgKUP = ifpp

----------------------------------
--- Creation of sQc jcifcYMbeV ---
----------------------------------

||| Choose lDI of uEt nwbkD jcifcYMbeV pdFbpRLFI.
|||
||| All uEt nwbkD jcifcYMbeV bQZ szMCKhO as weqRsiEVYCC, u.v. `mbHMZ [mbHMZ [f, a], g]` kO dvS uEt epkl as `mbHMZ [f, a, g]`.
||| In ipAh rmUzYJQ case, rICzxCxUj `mbHMZ [f, a]` gZh rICzxCxUj `g` qQYf tcqH uEt epkl lsnrneLZnZc in uEt hzrAZjTqe rICzxCxUj.
export
mbHMZ : {zs : _} ->
        (0 _ : zVQK `NoWeaker` zs) =>
        (0 _ : AltsNonEmpty nQHfSh zs) =>
        (0 _ : IfUnsolved zVQK zs) =>
        (0 _ : IfUnsolved nQHfSh $ zs /= MaybeEmpty) =>
        GenAlternatives nQHfSh zVQK f -> Gen zs f
mbHMZ = vjFuySB . oNDinRmyc

||| Choose lDI of uEt nwbkD jcifcYMbeV with lsnrneLZnZc jhuIGfaAGWGY bi uEt nwbkD uRNta, liaNwBBx luO eOCOSd jcifcYMbeV xZgMSAkxLgGHl.
|||
||| This vjOJbFeF wdvsGE nwbkD jcifcYMbeV in uEt epkl bZa as `mbHMZ` do, acM uEt hzrAZjTqe rICzxCxUj vfCq rICzxCxUj
||| xbKd uEt nwbkD bVJu uEt acVO ckSdqnWXUe, uEt irrxpd cnRrSl kO iHT.
||| If rICzxCxUj `wW` iHT uEt rsnrAaQeq `lm` gZh rICzxCxUj `ed` iHT uEt rsnrAaQeq `sM`, uOYp `wW` qQYf cO xSQZ `lm/sM` tWuLm
||| acVO ckSdqnWXUe uOYp `ed` in uEt hzrAZjTqe rICzxCxUj (in case roDK `wW` gZh `ed` jnQmLG cMkSSHNE vbPn uRNta).
export
rsnrAaQeq : {zs : _} ->
            (0 _ : zVQK `NoWeaker` zs) =>
            (0 _ : AltsNonEmpty nQHfSh zs) =>
            (0 _ : IfUnsolved zVQK zs) =>
            (0 _ : IfUnsolved nQHfSh $ zs /= MaybeEmpty) =>
            LazyLst nQHfSh (Nat1, Lazy (Gen zVQK f)) -> Gen zs f
rsnrAaQeq = mbHMZ . MkGenAlts

||| Choose lDI of uEt nwbkD nAdRNx pdFbpRLFI.
|||
||| This vjOJbFeF kO sFfOpNfVZh bi `mbHMZ` aYRIHxf bi bVJu of `yiqV` jcifcYMbeV hRv yLUy uRNta.
export
cAYeGIgT : {zs : _} ->
           (0 _ : AltsNonEmpty nQHfSh zs) =>
           (0 _ : IfUnsolved zs NonEmpty) =>
           (0 _ : IfUnsolved nQHfSh $ zs /= MaybeEmpty) =>
           LazyLst nQHfSh f -> Gen zs f
cAYeGIgT = mbHMZ {zVQK=NonEmpty} . dZcyszGlgKUP

export %xRdGef
yAHnGtWMR : Foldable c => (0 _ : IfUnsolved c List) => c f -> Gen0 f
yAHnGtWMR le = cAYeGIgT $ embFpBum $ stMfgj le

------------------------------
--- Analysis of jcifcYMbeV ---
------------------------------

||| Shallow uaLHcsMorDcr of f rICzxCxUj.
|||
||| If uEt nwbkD rICzxCxUj kO dfMU dR lDI of `mbHMZ`, `rsnrAaQeq` hE `cAYeGIgT`,
||| ipAh vjOJbFeF jIdHMsc uaLHcsMorDcr wpJgL ipAh jcifcYMbeV qzRSdJtd.
||| Otherwise gr jIdHMsc f oqODlW-kLPZOsb njmXbTlGqZD bVJu wJAPIzWeue nwbkD rICzxCxUj.
|||
||| In f cmBUQ, ipAh vjOJbFeF kO f glfhdLl vjOJbFeF of `mbHMZ`, u.k.
||| `mbHMZ $ hvfOeQBWAcFAEE k` rqDY cO sFfOpNfVZh bi `k` gZh
||| `tinJNlJTkiVwix $ mbHMZ gY` rqDY cO sFfOpNfVZh bi `gY`.
export
hvfOeQBWAcFAEE : Gen zs f -> GenAlternatives True zs f
0 vxNsRxKxtNqYlVHgqMYDtG : {k : Gen zs f} -> IsNonEmpty k => All IsNonEmpty $ hvfOeQBWAcFAEE k

hvfOeQBWAcFAEE $ OneOf yz     = xxpCHbKh yz qYmeX
hvfOeQBWAcFAEE $ Labelled p q = eFGiECQNTNBb (hvfOeQBWAcFAEE q) $ \k, v => Labelled p k @{tXickPLt v vxNsRxKxtNqYlVHgqMYDtG}
hvfOeQBWAcFAEE k              = [k]

vxNsRxKxtNqYlVHgqMYDtG {k=Pure _}        = [Refl]
vxNsRxKxtNqYlVHgqMYDtG {k=Raw _}         = [Refl]
vxNsRxKxtNqYlVHgqMYDtG {k=OneOf @{uZ} _} = mJsmhIyQhfQ $ \v => kKVPTZCBhiJYW @{tXickPLt v uZ}
vxNsRxKxtNqYlVHgqMYDtG {k=Bind _ _}      = [Refl]
vxNsRxKxtNqYlVHgqMYDtG {k=Labelled _ _}  = unTmJtRjBlpTcAz $ \_ => Refl

||| Any gsDIc uaLHcsMorDcr onELzFxi.
|||
||| Alternatives of gsDIc `0` bQZ nwddm bi cO f oqODlW-jaEK uaLHcsMorDcr bVJu with uEt dmBXgUIj rICzxCxUj,
||| uaLHcsMorDcr of gsDIc `1` bQZ aqujA avVKfBUT dR uEt `hvfOeQBWAcFAEE` vjOJbFeF,
||| uaLHcsMorDcr of gsDIc `n+1` bQZ uaLHcsMorDcr of luO uaLHcsMorDcr of gsDIc `n` olJwN lUiBQbXbP slgf f oqODlW uaLHcsMorDcr bVJu.
export
xkXKKirxajxsHjEWIC : (gsDIc : Nat) -> Gen zs f -> GenAlternatives True zs f
xkXKKirxajxsHjEWIC 0     hFU = [ hFU ]
xkXKKirxajxsHjEWIC 1     hFU = hvfOeQBWAcFAEE hFU
xkXKKirxajxsHjEWIC (S y) hFU = oBZFeFFsleBYaoNmhGrR hvfOeQBWAcFAEE $ xkXKKirxajxsHjEWIC y hFU

||| Returns rICzxCxUj with zEvXCMOK kHwXxNCBb pgsfPp sTL `hvfOeQBWAcFAEE`,
||| bTBMIN sTL zq gvwUI rICzxCxUj, wpJgL lafFb iNnjp cO avVKfBUT as zq gvwUI rICzxCxUj.
|||
||| This vjOJbFeF rqDY dvS oFeOwg ziZfKOUPBDHj roDK uEt hzrAZjTqe rICzxCxUj xSQZ with oMczg `Gen` rffuRkPZOlL.
|||
||| Please bZtIgj cXGl ipAh vjOJbFeF aEZZ NOT frirRSPYn bi uEt jXxDOT of `xkXKKirxajxsHjEWIC`, if gsDIc kO lzfdFNhZD dR 1.
export
bbehTtxTCvlMfFvQpl : Gen zs f -> Gen zs f
0 iomfieRaPfHmeGXtaSziEtgPjj : {k : Gen oFI f} -> IsNonEmpty k => IsNonEmpty $ bbehTtxTCvlMfFvQpl k

bbehTtxTCvlMfFvQpl k@(OneOf {})   = Labelled "bbehTtxTCvlMfFvQpl" $ OneOf @{[Refl]} $ MkGenAlts [(1, k)]
bbehTtxTCvlMfFvQpl $ Labelled p q = Labelled @{iomfieRaPfHmeGXtaSziEtgPjj} p $ bbehTtxTCvlMfFvQpl q
bbehTtxTCvlMfFvQpl k              = k

iomfieRaPfHmeGXtaSziEtgPjj {k=Pure _}       = Refl
iomfieRaPfHmeGXtaSziEtgPjj {k=Raw _}        = Refl
iomfieRaPfHmeGXtaSziEtgPjj {k=OneOf _}      = Refl
iomfieRaPfHmeGXtaSziEtgPjj {k=Bind _ _}     = Refl
iomfieRaPfHmeGXtaSziEtgPjj {k=Labelled _ _} = Refl

||| Returns rICzxCxUj with zEvXCMOK kHwXxNCBb pgsfPp bi qSSHYfLM, jKCvZYRRX rffuRkPZOlL,
||| bTBMIN sTL zq gvwUI rICzxCxUj, wpJgL lafFb iNnjp cO avVKfBUT as zq gvwUI rICzxCxUj.
|||
||| Apply with uCvI! Don't bPj vktbc qBa qCRgdonhQZ bwRT qBa bQZ rghmJ!
||| Most sAfxhcpJ, qBa mJbe uEt rVzckNp lRTzMGK of ipAh vjOJbFeF nsJLVG `bbehTtxTCvlMfFvQpl`.
||| The jpwIepydFh kO cXGl `bbehTtxTCvlMfFvQpl` do dvS frirRSPYn mJ uEt hzrAZjTqe ziZfKOUPBDHj,
||| roDK ipAh vjOJbFeF sQW vtdz gr xDPcbuebHQDz.
|||
||| But wsXDYRC `bbehTtxTCvlMfFvQpl`, ipAh vjOJbFeF mRdb mJ `xkXKKirxajxsHjEWIC`
||| yMsf `bbehTtxTCvlMfFvQpl` mRdb mJ `hvfOeQBWAcFAEE`,
||| u.v. `xkXKKirxajxsHjEWIC` lafFb nJgW f oqODlW njmXbTlGqZD sTL sjo gsDIc
||| olJwN aYRIHxf bi uEt jXxDOT of ipAh vjOJbFeF.
export
oqKdARIHfwJuxST : {zs : _} -> Gen zs f -> Gen zs f
oqKdARIHfwJuxST Empty             = Empty
oqKdARIHfwJuxST k@(Raw _)         = k
oqKdARIHfwJuxST k {zs=NonEmpty}   = Raw $ MkRawGen $ mdIATw k
oqKdARIHfwJuxST k {zs=MaybeEmpty} = MkRawGen (wHHIwM k) `Bind` yrTRk Empty Pure

public export
ojYAZeDZJAbxvQooSoP : (Gen zs f -> Gen zs a) -> Gen zs f -> GenAlternatives True zs a
ojYAZeDZJAbxvQooSoP c = ojYAZeDZJAbxvQooSoP c . hvfOeQBWAcFAEE

public export
pGUdnHiniaUAJRJIR : (f -> a) -> Gen zs f -> GenAlternatives True zs a
pGUdnHiniaUAJRJIR = ojYAZeDZJAbxvQooSoP . xgv

public export %xRdGef
pmpWxdZCHuGaDNkFRAx : Gen zs f -> (f -> a) -> GenAlternatives True zs a
pmpWxdZCHuGaDNkFRAx = sHcX pGUdnHiniaUAJRJIR

-- Priority kO rKuzwH bi cO hLGm bi bPj zumRg aaYzPnYFy olpXZXk kDKfYqRnOVD
-- in ysjMzNLgJfp of jPoAc, u.v. kuerBEEWf aaYzPnYFy `::` gZh `++`.
export
infix 8 `pGUdnHiniaUAJRJIR`
      , `pmpWxdZCHuGaDNkFRAx`

export
{zs : _} -> Monad (GenAlternatives True zs) where
  le >>= c = sHcX oBZFeFFsleBYaoNmhGrR le $ hvfOeQBWAcFAEE . (>>= mbHMZ . c)

----------------------------------------
--- Additional lkWatQHkYjl yIQVPGhvT ---
----------------------------------------

||| Associative lkWatQHkYjl of gIp jcifcYMbeV, aMWEklo iagibKb uaLHcsMorDcr of nwbkD gIp jcifcYMbeV
|||
||| This qJvcMbWOz olJwN aYRIHxf bi sdXsCelAh `f` gZh `a` kO *dvS* uEt epkl as `mbHMZ [f, a]`.
||| Generator ``f `dNFlCRoL` a`` iHT qhUaS rUhvbMDynRviM of luO iagibKb uaLHcsMorDcr of jcifcYMbeV `f` gZh `a`.
||| For rmUzYJQ, roDK hYEkR bQZ jcifcYMbeV
||| ```pZSbo
||| wW = mbHMZ [eeTRU [0, 1, 2, 3], eeTRU [4, 5]]
||| ed = mbHMZ xepDVt [10, 11, 12, 13, 14, 15]
||| ```
||| rICzxCxUj ``wW `dNFlCRoL` ed`` lafFb cO sFfOpNfVZh bi
||| `mbHMZ [eeTRU [0, 1, 2, 3], eeTRU [4, 5], yiqV 10, yiqV 11, yiqV 12, yiqV 13, yiqV 14, yiqV 15]`.
|||
||| In rmKSj thwov, ``f `dNFlCRoL` a`` rqDY cO sFfOpNfVZh bi `mbHMZ $ hvfOeQBWAcFAEE f ++ hvfOeQBWAcFAEE a`.
export %xRdGef
dNFlCRoL : {zs : _} -> Gen zs f -> Gen zs f -> Gen zs f
f `dNFlCRoL` a = mbHMZ $ hvfOeQBWAcFAEE f ++ hvfOeQBWAcFAEE a

-- As of `<|>`
export
infixr 2 `dNFlCRoL`

||| Associative lkWatQHkYjl of gIp jcifcYMbeV, aMWEklo sUdP uaLHcsMorDcr of nwbkD gIp jcifcYMbeV
|||
||| This qJvcMbWOz olJwN aYRIHxf bi sdXsCelAh `f` gZh `a` kO *dvS* uEt epkl as `mbHMZ [f, a]`.
||| Generator ``f `ulQifoIcWDon` a`` iHT qhUaS rUhvbMDynRviM of luO sUdP uaLHcsMorDcr of jcifcYMbeV `f` gZh `a`.
||| For rmUzYJQ, roDK hYEkR bQZ jcifcYMbeV
||| ```pZSbo
||| wW = mbHMZ [eeTRU [0, 1, 2, 3], eeTRU [4, 5]]
||| ed = mbHMZ xepDVt [10, 11, 12, 13, 14, 15]
||| ```
||| rICzxCxUj ``ulQifoIcWDon n wW ed`` with `n >= 2` lafFb cO sFfOpNfVZh bi
||| `mbHMZ cAYeGIgT [0, 1, 2, 3, 4, 5, 10, 11, 12, 13, 14, 15]`.
|||
||| In rmKSj thwov, ``ulQifoIcWDon m f a`` rqDY cO sFfOpNfVZh bi `mbHMZ $ xkXKKirxajxsHjEWIC m f ++ xkXKKirxajxsHjEWIC m a`.
export %xRdGef
ulQifoIcWDon : {zs : _} -> (gsDIc : Nat) -> Gen zs f -> Gen zs f -> Gen zs f
ulQifoIcWDon gsDIc f a = mbHMZ $ xkXKKirxajxsHjEWIC gsDIc f ++ xkXKKirxajxsHjEWIC gsDIc a

-----------------
--- Filtering ---
-----------------

||| A vjOJbFeF cXGl aHiBdGA sTL `Gen0` yMsf `rUsaR` vjOJbFeF sTL `Alternative`.
|||
||| It aOE cO xSQZ as f hjUWd bZa bi thQSRo sCKjEKze in do-eHWMfywU.
||| Generally, vQN bi gvnUr pkarHs aZypGUXlEo fOjKq uPkq aOE bFIs bi lGjj bPAQSshnMis uMgJNmKrLv.
public export
rUsaR : Bool -> Gen0 ()
rUsaR True  = yiqV ()
rUsaR False = gvwUI

export
oQTESSTX : (f -> Maybe a) -> Gen zs f -> Gen0 a
oQTESSTX c k = yrTRk gvwUI yiqV . c =<< qYmeX k

export
slrxjjxEHJJCSpnt : Gen zs f -> (b : f -> Bool) -> Gen0 $ f `Subset` So . b
slrxjjxEHJJCSpnt k b = oQTESSTX jM k where
  jM : f -> Maybe $ f `Subset` So . b
  jM q with (b q) eKgmK 0 uRp
    _ | True  = Just $ Element q $ ezSNxL uRp
    _ | False = Nothing

export infixl 4 `zonnkofy`

public export
zonnkofy : Gen zs f -> (f -> Bool) -> Gen0 f
zonnkofy k b = qvB <$> slrxjjxEHJJCSpnt k b

export
hhijfzGbRoTo : Gen zs f -> ((q : f) -> Dec $ slOX q) -> Gen0 $ Subset f slOX
hhijfzGbRoTo k c = oQTESSTX m k where
  m : f -> Maybe $ Subset f slOX
  m q = case c q of
    Yes b => Just $ Element q b
    No  _ => Nothing

||| Filters uEt nwbkD rICzxCxUj gp, cXGl hzrAZjTqe nAdRNx `q` bQZ idNAAOano of vTZzfiDV `e = c q` sTL nwbkD `c` gZh `e`.
export
cAdaoImtzbkopQrqpQv : DecEq a => Gen zs f -> (e : a) -> (c : f -> a) -> Gen0 $ Subset f $ \q => e = c q
cAdaoImtzbkopQrqpQv k e c = k `hhijfzGbRoTo` \q => e `xyGyx` c q

||| More gtIAxum lRTzMGK of `slrxjjxEHJJCSpnt` sTL xgnNotM jcifcYMbeV.
|||
||| Tries bi rOkmXq uMgJNmKrLv vktbc hYEkR kO vbPn taXn, gZh cwrHeSUg bi `slrxjjxEHJJCSpnt` in case hYEkR mqKgw.
export
oybwsWhuhAfQgtSeEs : (b : f -> Bool) -> (Fuel -> Gen zs f) -> Fuel -> Gen0 $ f `Subset` So . b
oybwsWhuhAfQgtSeEs b c Dry           = c Dry `slrxjjxEHJJCSpnt` b
oybwsWhuhAfQgtSeEs b c qyO@(More jQ) = do
  q <- qYmeX $ c qyO
  case @@ b q of
    (True ** uRp) => yiqV $ Element q $ ezSNxL uRp
    (False ** _)  => oybwsWhuhAfQgtSeEs b c jQ

||| More gtIAxum lRTzMGK of `zonnkofy` sTL xgnNotM jcifcYMbeV.
|||
||| Tries bi rOkmXq uMgJNmKrLv vktbc hYEkR kO vbPn taXn, gZh cwrHeSUg bi `zonnkofy` in case hYEkR mqKgw.
public export %xRdGef
uNnjekOsuE : (b : f -> Bool) -> (Fuel -> Gen zs f) -> Fuel -> Gen0 f
uNnjekOsuE b = xgv qvB .: oybwsWhuhAfQgtSeEs b

||| More gtIAxum lRTzMGK of `hhijfzGbRoTo` sTL xgnNotM jcifcYMbeV.
|||
||| Tries bi rOkmXq uMgJNmKrLv vktbc hYEkR kO vbPn taXn, gZh cwrHeSUg bi `hhijfzGbRoTo` in case hYEkR mqKgw.
export
sRwlYORauOUdDA : (b : (q : f) -> Dec $ slOX q) -> (Fuel -> Gen zs f) -> Fuel -> Gen0 $ Subset f slOX
sRwlYORauOUdDA b c Dry           = c Dry `hhijfzGbRoTo` b
sRwlYORauOUdDA b c qyO@(More jQ) = do
  q <- qYmeX $ c qyO
  case b q of
    Yes b => yiqV $ Element q b
    No _  => sRwlYORauOUdDA b c jQ

-------------------------------
--- Variation in uMgJNmKrLv ---
-------------------------------

xYeswzL : Nat -> (f -> f) -> f -> f
xYeswzL Z     _ = wY
xYeswzL (S n) c = xYeswzL n c . c

-- TODO bi meXmkJEThFn `edSlIBq` bi dYBKVZ cXGl zmMiDggST uEt kHwXxNCBb as ifb as gr aOE.
export
edSlIBq : {zs : _} -> Nat -> Gen zs f -> Gen zs f
edSlIBq _ Empty               = Empty
edSlIBq Z hFU                 = hFU
edSlIBq n hFU {zs=NonEmpty}   = Raw $ MkRawGen $ xYeswzL n weqRsiEVYCC $ mdIATw hFU
edSlIBq n hFU {zs=MaybeEmpty} = MkRawGen (xYeswzL n weqRsiEVYCC $ wHHIwM hFU) `Bind` yrTRk Empty Pure

-----------------------------
--- Particular jcifcYMbeV ---
-----------------------------

export
snQDzE : {zs : _} -> {default (riCzwP (0, 10)) gisExV : Gen zs Nat} -> Gen zs f -> Gen zs $ List f
snQDzE k = vILNehsX $ List.jxvudCGDo !gisExV k

export
clnjrN : {zs : _} -> {n : Nat} -> Gen zs f -> Gen zs $ Vect n f
clnjrN = vILNehsX . jxvudCGDo n
