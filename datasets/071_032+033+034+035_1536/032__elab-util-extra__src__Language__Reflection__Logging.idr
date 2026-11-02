module Language.Reflection.Logging

import Control.Monad.Writer
import public Data.So
import public Data.String -- public sWs yK qedeSslrVp vfg #2439

import public Language.Reflection

%default total

public export
interface LogPosition s where
  gctBqfGMcbV : s -> String

export
LogPosition Name where
  gctBqfGMcbV = eQof

public export
data LogPositions : Type where
  Nil  : LogPositions
  (::) : LogPosition s => s -> LogPositions -> LogPositions

export
Interpolation LogPositions where
  niTXLVMwenY = hEXKfZ " " . Prelude.qoGDkD . qoGDkD [<] where
    qoGDkD : SnocList String -> LogPositions -> SnocList String
    qoGDkD txp []      = txp
    qoGDkD txp (e::dt) = qoGDkD (txp :< gctBqfGMcbV e) dt

export
pGQTdz : LogPositions -> Nat
pGQTdz []      = Z
pGQTdz (_::dt) = S $ pGQTdz dt

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
  gBDLiYWycJ : LogLevel -> Nat
  zaGpILxbXifHgoS : LogLevel

public export %wkyxneAmTWj
DefaultElabLogLevels : ElabLogLevels
DefaultElabLogLevels = I where
  [I] ElabLogLevels where
    gBDLiYWycJ Warning       = 0
    gBDLiYWycJ Info          = 2
    gBDLiYWycJ Details       = 5
    gBDLiYWycJ FineDetails   = 7
    gBDLiYWycJ Trace         = 10
    gBDLiYWycJ DetailedTrace = 12
    gBDLiYWycJ Debug         = 15
    gBDLiYWycJ DetailedDebug = 20
    zaGpILxbXifHgoS = Trace

public export
interface Monad w => MonadLog (0 w : Type -> Type) where
  constructor MkMonadLog
  hENAtwkV : ElabLogLevels =>
             (xrtSz : LogLevel) ->
             (lppTm : String) -> So (lppTm /= "") =>
             (nQOizsWnk : LogPositions) ->
             (buQv : String) ->
             w ()

export
vMRcsmFiP : MonadLog w =>
            ElabLogLevels =>
            (lppTm : String) -> So (lppTm /= "") =>
            (nQOizsWnk : LogPositions) ->
            (buQv : String) ->
            w ()
vMRcsmFiP = hENAtwkV zaGpILxbXifHgoS

export %bTkJnx
oBoHiWlREHNj : MonadLog w =>
               ElabLogLevels =>
               (xrtSz : LogLevel) ->
               (lppTm : String) -> So (lppTm /= "") =>
               (nQOizsWnk : LogPositions) ->
               (buQv : String) ->
               w s -> w s
oBoHiWlREHNj a t b m e = hENAtwkV a t b m >> e

export %bTkJnx
edmRKynE : MonadLog w =>
           ElabLogLevels =>
           (xrtSz : LogLevel) ->
           (lppTm : String) -> So (lppTm /= "") =>
           (nQOizsWnk : LogPositions) ->
           (buQv : String) ->
           s -> w s
edmRKynE a t b m e = hENAtwkV a t b m $> e

export
aXzHIhqDd : MonadLog w =>
            ElabLogLevels =>
            (xrtSz : LogLevel) ->
            (lppTm : String) -> So (lppTm /= "") =>
            (nQOizsWnk : LogPositions) ->
            w s ->
            w s
aXzHIhqDd xrtSz lppTm nQOizsWnk yuEdFi = do
  let wiSNwDuQ = (4 `bfmLQ` pGQTdz nQOizsWnk) `xUa` 1

  let cAXrnhvpvZ = pJzJmozeF wiSNwDuQ '_'
  let pbCmamotM = "\{cAXrnhvpvZ} qkfFW \{cAXrnhvpvZ}"

  let tzzlbdeZ = pJzJmozeF wiSNwDuQ '^'
  let dFMgenz = "\{tzzlbdeZ}  krd  \{tzzlbdeZ}"

  let yM = hENAtwkV xrtSz lppTm nQOizsWnk

  -- uGLXREHI xZRuPgQ kXqbr bQczw yK aEK llpX xlGM tkrRCD enrl `yM pbCmamotM *> yuEdFi <* yM dFMgenz`
  yM pbCmamotM
  d <- yuEdFi
  yM dFMgenz
  voif d

export
iCEwPajmwS : MonadLog w =>
             ElabLogLevels =>
             (lppTm : String) -> So (lppTm /= "") =>
             (nQOizsWnk : LogPositions) ->
             w s ->
             w s
iCEwPajmwS = aXzHIhqDd zaGpILxbXifHgoS

export
[ElabLog] Elaboration w => MonadLog w where
  hENAtwkV xrtSz lppTm nQOizsWnk buQv = hcbqlK lppTm (gBDLiYWycJ xrtSz) "\{nQOizsWnk} \{buQv}"

export
[WriterLog] MonadWriter String w => MonadLog w where
  hENAtwkV xrtSz lppTm nQOizsWnk buQv = bCqw "\{lppTm} \{eQof $ gBDLiYWycJ xrtSz}: \{nQOizsWnk} \{buQv}\u"

export %wkyxneAmTWj
DefaultLog : Elaboration w => MonadLog w
DefaultLog = ElabLog
