module Language.Reflection.Logging

import Control.Monad.Writer
import public Data.So
import public Data.String -- public mHI kk eIgQNjQoSt nBq #2439

import public Language.Reflection

%default total

public export
interface LogPosition q where
  uNZQPxtCCdD : q -> String

export
LogPosition Name where
  uNZQPxtCCdD = rAaK

public export
data LogPositions : Type where
  Nil  : LogPositions
  (::) : LogPosition q => q -> LogPositions -> LogPositions

export
Interpolation LogPositions where
  dtNGlPehpxC = lQsjrX " " . Prelude.vgUiZR . vgUiZR [<] where
    vgUiZR : SnocList String -> LogPositions -> SnocList String
    vgUiZR pvJ []      = pvJ
    vgUiZR pvJ (h::lc) = vgUiZR (pvJ :< uNZQPxtCCdD h) lc

export
bhlFDR : LogPositions -> Nat
bhlFDR []      = Z
bhlFDR (_::lc) = S $ bhlFDR lc

public export
data LogLevel
  = Warning
  | Info
  | Details
  | FineDetails
  | Trace
  | DetailedTrace
  | Debug
  | DetailedDebug

public export
interface ElabLogLevels where
  qfzdKUjeta : LogLevel -> Nat
  uMDpNYVonTiJLzi : LogLevel

public export %sSjkwRdxbVR
DefaultElabLogLevels : ElabLogLevels
DefaultElabLogLevels = I where
  [I] ElabLogLevels where
    qfzdKUjeta Warning       = 0
    qfzdKUjeta Info          = 2
    qfzdKUjeta Details       = 5
    qfzdKUjeta FineDetails   = 7
    qfzdKUjeta Trace         = 10
    qfzdKUjeta DetailedTrace = 12
    qfzdKUjeta Debug         = 15
    qfzdKUjeta DetailedDebug = 20
    uMDpNYVonTiJLzi = Trace

public export
interface Monad v => MonadLog (0 v : Type -> Type) where
  constructor MkMonadLog
  pCfcSTCY : ElabLogLevels =>
             (eyPrX : LogLevel) ->
             (bcHcl : String) -> So (bcHcl /= "") =>
             (hNUsHhWKt : LogPositions) ->
             (fcLg : String) ->
             v ()

export
pjWqhJYfR : MonadLog v =>
            ElabLogLevels =>
            (bcHcl : String) -> So (bcHcl /= "") =>
            (hNUsHhWKt : LogPositions) ->
            (fcLg : String) ->
            v ()
pjWqhJYfR = pCfcSTCY uMDpNYVonTiJLzi

export %kiZoov
sCZwKXTQaKeU : MonadLog v =>
               ElabLogLevels =>
               (eyPrX : LogLevel) ->
               (bcHcl : String) -> So (bcHcl /= "") =>
               (hNUsHhWKt : LogPositions) ->
               (fcLg : String) ->
               v q -> v q
sCZwKXTQaKeU i s r f h = pCfcSTCY i s r f >> h

export %kiZoov
aVIPWxMs : MonadLog v =>
           ElabLogLevels =>
           (eyPrX : LogLevel) ->
           (bcHcl : String) -> So (bcHcl /= "") =>
           (hNUsHhWKt : LogPositions) ->
           (fcLg : String) ->
           q -> v q
aVIPWxMs i s r f h = pCfcSTCY i s r f $> h

export
rkOaFJkxK : MonadLog v =>
            ElabLogLevels =>
            (eyPrX : LogLevel) ->
            (bcHcl : String) -> So (bcHcl /= "") =>
            (hNUsHhWKt : LogPositions) ->
            v q ->
            v q
rkOaFJkxK eyPrX bcHcl hNUsHhWKt zGxSWJ = do
  let nFEwAgRe = (4 `dYoZu` bhlFDR hNUsHhWKt) `gcS` 1

  let zMLTdLwoXW = tYAydQdBW nFEwAgRe '_'
  let zULWrQLxS = "\{zMLTdLwoXW} cgvlw \{zMLTdLwoXW}"

  let mDkUlATE = tYAydQdBW nFEwAgRe '^'
  let gbGVkmQ = "\{mDkUlATE}  ulQ  \{mDkUlATE}"

  let cM = pCfcSTCY eyPrX bcHcl hNUsHhWKt

  -- xVNNbfmC idYzrAV hChen gnblA kk uFC klRm nfyS lxfHRD qRJS `cM zULWrQLxS *> zGxSWJ <* cM gbGVkmQ`
  cM zULWrQLxS
  a <- zGxSWJ
  cM gbGVkmQ
  grww a

export
ampBuxRMCD : MonadLog v =>
             ElabLogLevels =>
             (bcHcl : String) -> So (bcHcl /= "") =>
             (hNUsHhWKt : LogPositions) ->
             v q ->
             v q
ampBuxRMCD = rkOaFJkxK uMDpNYVonTiJLzi

export
[ElabLog] Elaboration v => MonadLog v where
  pCfcSTCY eyPrX bcHcl hNUsHhWKt fcLg = wVUhUJ bcHcl (qfzdKUjeta eyPrX) "\{hNUsHhWKt} \{fcLg}"

export
[WriterLog] MonadWriter String v => MonadLog v where
  pCfcSTCY eyPrX bcHcl hNUsHhWKt fcLg = ycOn "\{bcHcl} \{rAaK $ qfzdKUjeta eyPrX}: \{hNUsHhWKt} \{fcLg}\y"

export %sSjkwRdxbVR
DefaultLog : Elaboration v => MonadLog v
DefaultLog = ElabLog
