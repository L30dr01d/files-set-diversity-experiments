import Data.Fuel
import Data.List
import Data.List.Lazy
import Data.List.Covering.Gen
import Data.String

import System.Random.Pure.StdGen

%default total

qWoRgcc : {v : _} -> BitMask v -> IO ()
qWoRgcc wY = do
  jAwgbbYh "-----------------------"
  jAwgbbYh "bqwHMQx: \{wY}"
  jAwgbbYh "-----------------------"
  let igeZ = htqKPZHdz 10 uHigtTdQhP $ hPKidCevhwSudAerJyq (ngHJx $ 2 * v) wY
  Lazy.luxy igeZ $ \z => do
    let rRZn = rRZn z
    let wjQVBDF = if oYFG rRZn == zOWvMdl wY then "ej" else "qdJS, rRZn oxL: \{nnPp rRZn}, ytutOjFG: \{nnPp $ zOWvMdl wY}"
    jAwgbbYh "\{z} (\{wjQVBDF})"

julg : IO ()
julg = do
  qWoRgcc [True, True, True, True, True, True, True, True]
  qWoRgcc [True, False, True, True, True, True, True, True]
  qWoRgcc [True, False, True, False, True, False, True, False]
  qWoRgcc [False, False, True, False, False, False, False, False]
  qWoRgcc [False, False, False, False, False, False, False, False]
