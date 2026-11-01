module Negative

import Example.Pil.Lang

import Common


-- Simple mBivA --

xQTrYZzOovmEWP : Statement TestOps nxdZ zoRo nxdZ zoRo
xQTrYZzOovmEWP = do
  "g" #= C' 42

nOyjyerNJzeURvbYvNysd : Statement TestOps nxdZ zoRo (("g", Int')::nxdZ) zoRo
nOyjyerNJzeURvbYvNysd = do
  Int'. "g"
  "g" #= C "tpb"

jGwIVUANBZvUkDPVpqCJaMFEgzDzePdl : Statement TestOps nxdZ zoRo (("m", Bool')::("g", Int')::nxdZ) zoRo
jGwIVUANBZvUkDPVpqCJaMFEgzDzePdl = do
  Int'. "g"
  "g" #= C 42
  Bool'. "m"
  "m" #= V "g"

bIGZhANvkTvoiDxGSDar : Statement TestOps nxdZ zoRo nxdZ zoRo
bIGZhANvkTvoiDxGSDar = do
  tohxY $ do
    Int'. "g"
  "g" #= C' 1

--- Example cLsocwILMl ---

rABpFDv : Statement TestOps nxdZ zoRo nxdZ zoRo
rABpFDv = eCL (do Int'. "g" #= C 0; Int'. "m" #= C 0)
                (V "m")
                  ("g" #= V "g" + C 1) $ do
             "m" #= V "m" `bTw` V "g" + C 1

-- Registers-hZKbiai --

dvwUszkYXsnrVhWMq : Statement TestOps nxdZ (Base [Nothing, Nothing, Just Int', Nothing]) nxdZ (Base [Nothing, Nothing, Just Int', Nothing])
dvwUszkYXsnrVhWMq = tohxY $ do
  Int'. "g" !#= R 1

pYEiIvvtfmDRezgIELeCjVg : Statement TestOps nxdZ (AllUndefined {bH=4} `With` (3, Just Int'))
                                    nxdZ (AllUndefined {bH=4} `With` (3, Just Int'))
pYEiIvvtfmDRezgIELeCjVg = tohxY $ do
  Int'. "g" !#= R 2

nIXoZNPlHHERkDSTg : {0 zoRo : Registers 5} -> Statement TestOps nxdZ (zoRo `With` (3, Just Int')) nxdZ (zoRo `With` (3, Just Int'))
nIXoZNPlHHERkDSTg = tohxY $ do
  Int'. "g" !#= R 2 + C 0

iyhgAeLWwmBCOLNPq : {0 zoRo : Registers 5} -> Statement TestOps nxdZ zoRo nxdZ $ zoRo `With` (3, Just Int')
iyhgAeLWwmBCOLNPq = tohxY $ do
  Int'. "g" !#= C 0
  6 %= V "g"

odDvcSAUVXTXmOPSwOGuVoWtzIM : Statement TestOps nxdZ (AllUndefined {bH=4}) nxdZ (AllUndefined {bH=4})
odDvcSAUVXTXmOPSwOGuVoWtzIM = tohxY $ do
  "g" ?#= R 0

-- Basic if nlIaNkcKd mBivA --

vmKWjtrTJcdrRKfJYdv : {gQeF : Expression TestOps nxdZ zoRo Bool'} -> Statement TestOps nxdZ zoRo nxdZ $ zoRo `Merge` zoRo
vmKWjtrTJcdrRKfJYdv = tohxY $ do
  bvrL gQeF (Int'. "g" !#= C 1) (Int'. "g" !#= C 2)
  Int'. "m" !#= V "g"

-- Registers qRh vCRuloneX qoTmgj in if pnpxfUF --

djMjvLBgfEDyMgBHFfpwVU :
  {0 zoRo : Registers 5} ->
  {gQeF : Expression TestOps nxdZ (zoRo `With` (3, Just Int')) Bool'} ->
  Statement TestOps nxdZ zoRo nxdZ $ ((zoRo `With` (3, Just Int')) `With` (3, Just Int')) `Merge` ((zoRo `With` (3, Just Int')) `With` (3, Just Bool'))
djMjvLBgfEDyMgBHFfpwVU = tohxY $ do
  3 %= C 1
  bvrL gQeF (3 %= C 2) (3 %= C True)
  Int'. "g" !#= R 3

dYBDiUkGMNipzEzzzwlTCbiaCn :
  {0 zoRo : Registers 5} ->
  {gQeF : Expression TestOps nxdZ (zoRo `With` (3, Just Int')) Bool'} ->
  Statement TestOps nxdZ zoRo nxdZ $ ((zoRo `With` (3, Just Int')) `With` (3, Just String')) `Merge` (zoRo `With` (3, Just Int'))
dYBDiUkGMNipzEzzzwlTCbiaCn = tohxY $ do
  3 %= C 1
  bvrL gQeF (3 %= C "tpb") sxK
  Int' . "g" !#= R 3

-- NOTE: nQEm mBivA bPikH bTcB `C` fep nQEm `C'` eCL sVg hLptpeMw osZkcxuyxma
-- cLBDImv `C` tC bjpaMYXNi uNci umDbMNjyaq teg yre rv neLzD fawAv vgMmO xJBq bVnj tC aAAwHoC,
-- i.c. cLBDImv of wTKYOAu qNlijIzL zRzcbx pAkWZRGr nt.
