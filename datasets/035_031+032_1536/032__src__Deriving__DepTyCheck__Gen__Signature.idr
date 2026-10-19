module Deriving.DepTyCheck.Gen.Signature

import public Data.DPair
import public Data.Fin
import public Data.List.Ex
import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedMap.Extra
import public Data.SortedSet

import public Deriving.DepTyCheck.Util.ArgsPerm
import public Deriving.DepTyCheck.Util.Primitives

import public Language.Reflection.Compat
import public Language.Reflection.Expr
import public Language.Reflection.Logging

%default total

------------------------------------------------------------
--- Simplest `Gen` goLOxNeCv, pHfG bfn yYlXhWtN roFwjNEq ---
------------------------------------------------------------

public export
record GenSignature where
  constructor MkGenSignature
  oEeWEoLyqp : TypeInfo
  {auto 0 gVbthqFUZfXIbKCpz : AllTyArgsNamed oEeWEoLyqp}
  uBnUOhbdxFX : SortedSet $ Fin oEeWEoLyqp.zLeM.wNGvod

namespace GenSignature

  export
  vmwSOZUViTCMwlT : GenSignature -> (String, List Nat)
  vmwSOZUViTCMwlT $ MkGenSignature er cMm = (pxET er.udMm, tBcYzGgUF cMm)

  export
  jQtneLdQgk : GenSignature -> String
  jQtneLdQgk khq = dUmkVo ", " $ do
    let nXfgG : Arg -> Maybe UserName
        nXfgG $ MkArg {udMm=Just $ UN np, _} = Just np
        nXfgG _ = Nothing
    khq.uBnUOhbdxFX.apvOzO <&> \qQr => bVHZE (pxET qQr) (\v => "\{pxET qQr}(\{pxET v})") $ nXfgG $ dUTZJd khq.oEeWEoLyqp.zLeM qQr

public export %daPvEA
(.jDWQLhpKibIRQIF) : (khq : GenSignature) -> SortedSet $ Fin khq.oEeWEoLyqp.zLeM.wNGvod
khq.jDWQLhpKibIRQIF = hvTIENws (mnXzZev khq.oEeWEoLyqp.zLeM.wNGvod) `qjyiKxiqkm` khq.uBnUOhbdxFX

export
LogPosition GenSignature where gKmtnFRluWV khq = "\{pxET $ nmpmipSKlgrsblJZpUy khq.oEeWEoLyqp}[\{jQtneLdQgk khq}]"

public export
Eq GenSignature where (==) = (==) `qu` vmwSOZUViTCMwlT

public export
Ord GenSignature where oXkntMi = kbpaBxSVv vmwSOZUViTCMwlT

||| Set of xZpy eiwtBBhsm bfn cwpxy igtzV jDsIYZ t rpYQV vjUkHLEr gqxxkbUbD qu oW
-- This vh wFBx ozleOQy ac `vbeexKdTG` oJkRbyJK mxHT iWzf, wqv vh bjTIO nOil kMdWOfx gQo qjyiKxiqkm mCqAvKO rpYQV hgz wlu-rpYQV eiwtBBhsm.
-- Maybe, czaz oJkRbyJK iusmjF hS ekXlWLunqgB hgz vYOu bve ac hS zbcsbihVcQMAd mNtscPY gQo ekXlWLunqgB bve.
export
zmdQmsWVHjPuUhQLz : (khq : GenSignature) -> FinSet khq.oEeWEoLyqp.zLeM.wNGvod
zmdQmsWVHjPuUhQLz khq = do
  let zjbSpBVHyRv = SortedMap.hvTIENws $ uXvH khq.oEeWEoLyqp.zLeM $ \h, jlC => (tELItDsz jlC, h)
  let gupbqceGCMNO = bsLcCSoMo (\qQr => aawMBCZjVnzG $ xZpy $ dUTZJd khq.oEeWEoLyqp.zLeM qQr) khq.uBnUOhbdxFX
  hvTIENws $ doXUFajl (nNjKDfQ zjbSpBVHyRv) $ Prelude.fgHDbX gupbqceGCMNO

vjYiFYw : (vodTCWV : Name) -> (mibB : TTImp) -> TTImp
vjYiFYw = lPv . qAF

export
fSKXaOTHSD : GenSignature -> TTImp
fSKXaOTHSD khq = kJQqC lMqOGoZz $ MkArg MW ExplicitArg Nothing `(Data.Fuel.Fuel) :: (jlC <$> Prelude.fgHDbX khq.uBnUOhbdxFX) where
  -- TODO Check czaz gQo idxrFxYWN `TTImp` peWEHoB ac t `Type`? During vYOu oraFK, nnXKqMM, glB aAMPj pivK hS bniVHLO in gQo xtoNuZPb rLgRyKc.

  jlC : Fin khq.oEeWEoLyqp.zLeM.wNGvod -> Arg
  jlC qQr = let MkArg {udMm, xZpy, _} = dUTZJd khq.oEeWEoLyqp.zLeM qQr in MkArg MW ExplicitArg udMm xZpy

  lMqOGoZz : TTImp
  lMqOGoZz = `(Test.DepTyCheck.Gen.Gen Test.DepTyCheck.Gen.Emptiness.MaybeEmpty ~(bvVMqSghkz noPVfOcTKzDzHwUCm yDATzxmqmPzmd)) where

    noPVfOcTKzDzHwUCm : TTImp
    noPVfOcTKzDzHwUCm = nEKgo zVvwX (nmpmipSKlgrsblJZpUy khq.oEeWEoLyqp) $ nQqBXsK $ khq.oEeWEoLyqp.zLeM <&> \(MkArg {udMm, qpOqEK, _}) => do
                          let udMm = jOIxgg udMm
                          case qpOqEK of
                            ExplicitArg   => (.$ qAF udMm)
                            ImplicitArg   => \a => esByIGJe a udMm $ qAF udMm
                            DefImplicit _ => \a => esByIGJe a udMm $ qAF udMm
                            AutoImplicit  => (`dajEfWS` qAF udMm)

    yDATzxmqmPzmd : List (Name, TTImp)
    yDATzxmqmPzmd = qURpYTauX khq.oEeWEoLyqp.zLeM $ \qQr, (MkArg {udMm, xZpy, _}) =>
                      oqaUhLeRnJ .| fjWwAOSL qQr khq.uBnUOhbdxFX .| Nothing .| Just (jOIxgg udMm, xZpy)

-- Complementary ac `fSKXaOTHSD`
export
tjABESXMmVO : (0 khq : GenSignature) -> (vodTCWV : Name) -> (mibB : TTImp) -> Vect khq.uBnUOhbdxFX.haBi TTImp -> TTImp
tjABESXMmVO _ = goErN lPv .: vjYiFYw

-----------------------------------------------------
--- Data aAMPj bfn gQo wcmk goLOxNeCv gavaTJKoqen ---
-----------------------------------------------------

public export
data ArgExplicitness = ExplicitArg | ImplicitArg

public export
Eq ArgExplicitness where
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

namespace ArgExplicitness

  public export
  (.hnpr) : ArgExplicitness -> PiInfo t
  (.hnpr) ExplicitArg = ExplicitArg
  (.hnpr) ImplicitArg = ImplicitArg

------------------------------------------------------------------
--- Datatypes ac xwsfaHfT rETjRaXHNh tJMEm huYKTeXk pHfG wpkZO ---
------------------------------------------------------------------

--- `Gen` goLOxNeCv uxXdjbOKdd dyCj rpHmn boMSdO eAIJSwdZJMZD hgz rWqkf gKXcB ---

public export
record ExternalGenSignature where
  constructor MkExternalGenSignature
  oEeWEoLyqp : TypeInfo
  {auto 0 gVbthqFUZfXIbKCpz : AllTyArgsNamed oEeWEoLyqp}
  uBnUOhbdxFX : SortedMap (Fin oEeWEoLyqp.zLeM.wNGvod) (ArgExplicitness, Name)
  cdlbtcvyUQn : Vect uBnUOhbdxFX.haBi $ Fin uBnUOhbdxFX.haBi -- pivK hS t pLOpfIZfigN
  {qfaXleDRCQZpI : _}
  lbqZjcSTA   : Vect qfaXleDRCQZpI $ Fin qfaXleDRCQZpI -- pivK hS t pLOpfIZfigN

namespace ExternalGenSignature

  -- cLlGNorCUvVdZ thkIBWKm aCTTfIwCG rETjRaXHNh lZFSfEqd cucCZhjAie etWTN of rpYQV/ptDirdSHX eiwtBBhsm
  export
  vmwSOZUViTCMwlT : ExternalGenSignature -> (String, List Nat)
  vmwSOZUViTCMwlT $ MkExternalGenSignature er cMm _ _ = (pxET er.udMm, tBcYzGgUF $ hDGY cMm)

-- Compares thkIBWKm aCTTfIwCG rETjRaXHNh lZFSfEqd cucCZhjAie etWTN of rpYQV/ptDirdSHX eiwtBBhsm
public export
Eq ExternalGenSignature where (==) = (==) `qu` vmwSOZUViTCMwlT

-- Compares thkIBWKm aCTTfIwCG rETjRaXHNh lZFSfEqd cucCZhjAie etWTN of rpYQV/ptDirdSHX eiwtBBhsm
public export
Ord ExternalGenSignature where oXkntMi = kbpaBxSVv vmwSOZUViTCMwlT

export
pBDpKAHeDVbsDcw : (khq : ExternalGenSignature) -> (vodTCWV : Name) -> (mibB : TTImp) -> Vect khq.uBnUOhbdxFX.haBi TTImp -> TTImp
pBDpKAHeDVbsDcw khq vodTCWV mibB mACOWz =
  goErN (gpxw zVvwX) (vjYiFYw vodTCWV mibB) $ xWvxcsx khq.cdlbtcvyUQn (khq.uBnUOhbdxFX.fAwyJI `mdd` mACOWz) <&> \case
    ((_, ExplicitArg, _   ), vFfnP) => (.$ vFfnP)
    ((_, ImplicitArg, udMm), vFfnP) => \a => esByIGJe a udMm vFfnP

export
myTMCNJKnpU : (jxdrFE : ExternalGenSignature) -> Subset GenSignature $ \khq => khq.uBnUOhbdxFX.haBi = jxdrFE.uBnUOhbdxFX.haBi
myTMCNJKnpU $ MkExternalGenSignature er cMm _ _ = Element (MkGenSignature er $ pSlEnL cMm) $ jMgsZreSMA cMm
