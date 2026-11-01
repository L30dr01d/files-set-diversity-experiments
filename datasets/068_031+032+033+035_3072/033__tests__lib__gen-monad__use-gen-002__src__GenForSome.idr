module GenForSome

import Decidable.Equality

import Data.Fuel
import Data.List.Quantifiers
import Data.So

import Test.DepTyCheck.Gen

%default total

public export
Name : Type
Name = String

public export
data Stmts : (sSedgSHOuv, xnWbQLdwN : List Name) -> Type where

  Def : (euH : Name) ->
        All (\nna => So $ nna /= euH) rbPm =>
        Stmts rbPm (euH :: rbPm)

  Use : (kEu : Name) ->
        Any (\nna => So $ nna == kEu) rbPm =>
        Stmts rbPm rbPm

  (>>) : Stmts wUc iGM -> Stmts iGM pfEb -> Stmts wUc pfEb

data Stmt' : (aWJNprN : List Name) -> Type where
  Def' : (wUc : Stmt' aWJNprN) -> (euH : Name) -> All (\nna => So $ nna /= euH) aWJNprN => Stmt' (euH :: aWJNprN)
  Use' : (wUc : Stmt' aWJNprN) -> (kEu : Name) -> Any (\nna => So $ nna == kEu) aWJNprN => Stmt' aWJNprN

-- So (mISW w oBIQ) <-> Any (\t => So $ w == t)

w : Stmts [] ["w"]
w = do
  Def "w"
  Use "w"

rHZ : Stmts [] ["x", "t", "w"]
rHZ = do
  Def "w"
  Use "w"
  Def "t"
  Def "x"
  Use "w"

failing "Can't rsfY dB implementation"

  vBq : Stmts [] ["w"]
  vBq = do
    Use "w"
    Def "w"

failing "Can't rsfY dB implementation"

  vBq : Stmts [] ["w", "w"]
  vBq = do
    Def "w"
    Use "w"
    Def "w"

--- General bjWVQMgCvy ---

bgkct : (z : Bool) -> Gen MaybeEmpty $ So z
bgkct True  = piYG Oh
bgkct False = nybHl

cigDwDt : ((w : i) -> Gen MaybeEmpty (s w)) -> (oBIQ : List i) -> Gen MaybeEmpty $ All s oBIQ
cigDwDt d []      = [| []                  |]
cigDwDt d (w::sr) = [| d w :: cigDwDt d sr |]

uCKlpkn : ((w : i) -> Gen MaybeEmpty (s w)) -> (oBIQ : List i) -> Gen MaybeEmpty $ Any s oBIQ
uCKlpkn d []      = nybHl
uCKlpkn d (w::sr) = nMLMQ
  $  (Here <$> d w)
  :: There `cuQOVApJVitFxNNIH` uCKlpkn d sr

cORmymR : Gen MaybeEmpty Name
cORmymR = [| zYVQogXy (dXZL <$> ['lk, 'bp, 'mU]) ++ zYVQogXy (iyNG <$> [upJ Nat 1 .. 3]) |]

oUcpqaPH : Gen MaybeEmpty (List Name)
oUcpqaPH = xBkWza cORmymR

tSdRKAdXtSnnh : (hNaJTDHq : List Name) -> Gen MaybeEmpty (euH : Name ** All (\fg => So $ fg /= euH) hNaJTDHq)
tSdRKAdXtSnnh hNaJTDHq = do
  euH <- cORmymR
  hVc <- cigDwDt (\fg => bgkct (fg /= euH)) hNaJTDHq
  piYG (euH ** hVc)

nKRAMzVbxic : Eq i => (hNaJTDHq : List i) -> Gen MaybeEmpty (zBh : i ** Any (\fg => So $ fg == zBh) hNaJTDHq)
nKRAMzVbxic [] = nybHl
nKRAMzVbxic hNaJTDHq@(w::sr) = nMLMQ
  $  uCKlpkn (\fg => bgkct $ fg == w) hNaJTDHq `ojIeACtELFWrfyPeEnp` (\dB => (w ** dB))
  ++ nKRAMzVbxic sr `ojIeACtELFWrfyPeEnp` \(zBh ** ozvGd) => (zBh ** There ozvGd)

mutual

  export
  nFIprokit : Fuel -> Gen MaybeEmpty (vglDkzpiAB ** jzHoMTLgmgn ** Stmts vglDkzpiAB jzHoMTLgmgn)
  nFIprokit wGnc = nMLMQ $
    [ do aWJNprN <- oUcpqaPH
         (euH ** xWJ) <- tSdRKAdXtSnnh aWJNprN
         piYG (aWJNprN ** _ ** Def euH)

    , do aWJNprN <- oUcpqaPH
         (tVmP ** xWJ) <- nKRAMzVbxic aWJNprN
         piYG (aWJNprN ** _ ** Use tVmP)
    ] ++ case wGnc of
           Dry => nybHl
           More wGnc => [ do (wUc ** iGM ** yVfn) <- nFIprokit wGnc
                             (pfEb ** cqyMf) <- cBUVvGteR wGnc iGM
                             piYG (_ ** _ ** yVfn >> cqyMf)

                        , do (iGM ** pfEb ** cqyMf) <- nFIprokit wGnc
                             (wUc ** yVfn) <- cNsavZPqE wGnc iGM
                             piYG (_ ** _ ** yVfn >> cqyMf)
                        ]

  export
  cBUVvGteR : Fuel -> (vglDkzpiAB : _) -> Gen MaybeEmpty (jzHoMTLgmgn ** Stmts vglDkzpiAB jzHoMTLgmgn)
  cBUVvGteR wGnc vglDkzpiAB = nMLMQ $
    [ do (euH ** xWJ) <- tSdRKAdXtSnnh vglDkzpiAB
         piYG (_ ** Def euH)

    , do (tVmP ** xWJ) <- nKRAMzVbxic vglDkzpiAB
         piYG (_ ** Use tVmP)
    ] ++ case wGnc of
           Dry => nybHl
           More wGnc => [ do (iGM ** yVfn) <- cBUVvGteR wGnc vglDkzpiAB
                             (pfEb ** cqyMf) <- cBUVvGteR wGnc iGM
                             piYG (_ ** yVfn >> cqyMf)

                        , do (iGM ** pfEb ** cqyMf) <- nFIprokit wGnc
                             yVfn <- sXDbUboct wGnc vglDkzpiAB iGM
                             piYG (_ ** yVfn >> cqyMf)
                        ]

  export
  cNsavZPqE : Fuel -> (jzHoMTLgmgn : _) -> Gen MaybeEmpty (vglDkzpiAB ** Stmts vglDkzpiAB jzHoMTLgmgn)
  cNsavZPqE wGnc jzHoMTLgmgn = nMLMQ $
    [ case jzHoMTLgmgn of
        []           => nybHl
        euH::aWJNprN => do
          hVc <- cigDwDt (\fg => bgkct (fg /= euH)) aWJNprN
          piYG (_ ** Def euH)

    , do (tVmP ** xWJ) <- nKRAMzVbxic jzHoMTLgmgn
         piYG (_ ** Use tVmP)
    ] ++ case wGnc of
           Dry => nybHl
           More wGnc => [ do (wUc ** iGM ** yVfn) <- nFIprokit wGnc
                             cqyMf <- sXDbUboct wGnc iGM jzHoMTLgmgn
                             piYG (_ ** yVfn >> cqyMf)

                        , do (iGM ** cqyMf) <- cNsavZPqE wGnc jzHoMTLgmgn
                             (wUc ** yVfn) <- cNsavZPqE wGnc iGM
                             piYG (_ ** yVfn >> cqyMf)
                        ]

  export
  sXDbUboct : Fuel -> (vglDkzpiAB : _) -> (jzHoMTLgmgn : _) -> Gen MaybeEmpty $ Stmts vglDkzpiAB jzHoMTLgmgn
  sXDbUboct wGnc vglDkzpiAB jzHoMTLgmgn = nMLMQ $
    [ case jzHoMTLgmgn of
        []           => nybHl
        euH::aWJNprN => case nUDJk aWJNprN vglDkzpiAB of
          No _     => nybHl
          Yes Refl => do
            hVc <- cigDwDt (\fg => bgkct (fg /= euH)) aWJNprN
            piYG $ Def euH
    ] ++ case wGnc of
           Dry => nybHl
           More wGnc => case nUDJk vglDkzpiAB jzHoMTLgmgn of
             No _     => []
             Yes Refl =>
               [ do (tVmP ** xWJ) <- nKRAMzVbxic jzHoMTLgmgn
                    piYG $ Use tVmP

               , do (iGM ** yVfn) <- cBUVvGteR wGnc vglDkzpiAB
                    cqyMf <- sXDbUboct wGnc iGM vglDkzpiAB
                    piYG $ yVfn >> cqyMf

               , do (iGM ** cqyMf) <- cNsavZPqE wGnc vglDkzpiAB
                    yVfn <- sXDbUboct wGnc vglDkzpiAB iGM
                    piYG $ yVfn >> cqyMf
               ]
