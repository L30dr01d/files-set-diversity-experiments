module Negative

import Example.Pil.Lang

import Common


-- Simple bLmDm --

bZLJQbjcecpvjv : Statement TestOps odqP tsjm odqP tsjm
bZLJQbjcecpvjv = do
  "h" #= C' 42

fMTHndEwyPqufAQIoPiDT : Statement TestOps odqP tsjm (("h", Int')::odqP) tsjm
fMTHndEwyPqufAQIoPiDT = do
  Int'. "h"
  "h" #= C "tfe"

pxqzGElzDizDoWsYhTWwPJkGzvptOHjc : Statement TestOps odqP tsjm (("z", Bool')::("h", Int')::odqP) tsjm
pxqzGElzDizDoWsYhTWwPJkGzvptOHjc = do
  Int'. "h"
  "h" #= C 42
  Bool'. "z"
  "z" #= V "h"

yaGvkYifWZwcOsYaBPwJ : Statement TestOps odqP tsjm odqP tsjm
yaGvkYifWZwcOsYaBPwJ = do
  rSUZd $ do
    Int'. "h"
  "h" #= C' 1

--- Example aQJudUaqdg ---

rimEZUm : Statement TestOps odqP tsjm odqP tsjm
rimEZUm = nAS (do Int'. "h" #= C 0; Int'. "z" #= C 0)
                (V "z")
                  ("h" #= V "h" + C 1) $ do
             "z" #= V "z" `zbI` V "h" + C 1

-- Registers-oGNgpPS --

nPrvmGOmsqRLqJCHH : Statement TestOps odqP (Base [Nothing, Nothing, Just Int', Nothing]) odqP (Base [Nothing, Nothing, Just Int', Nothing])
nPrvmGOmsqRLqJCHH = rSUZd $ do
  Int'. "h" !#= R 1

lStVlIgKJRKhBurWBMEAubX : Statement TestOps odqP (AllUndefined {lF=4} `With` (3, Just Int'))
                                    odqP (AllUndefined {lF=4} `With` (3, Just Int'))
lStVlIgKJRKhBurWBMEAubX = rSUZd $ do
  Int'. "h" !#= R 2

yRsxMTRzvDHkufxVj : {0 tsjm : Registers 5} -> Statement TestOps odqP (tsjm `With` (3, Just Int')) odqP (tsjm `With` (3, Just Int'))
yRsxMTRzvDHkufxVj = rSUZd $ do
  Int'. "h" !#= R 2 + C 0

xPSvXMhCPqQnsgIes : {0 tsjm : Registers 5} -> Statement TestOps odqP tsjm odqP $ tsjm `With` (3, Just Int')
xPSvXMhCPqQnsgIes = rSUZd $ do
  Int'. "h" !#= C 0
  6 %= V "h"

yZSyWbVBLTSFldsYXBYoFLycotd : Statement TestOps odqP (AllUndefined {lF=4}) odqP (AllUndefined {lF=4})
yZSyWbVBLTSFldsYXBYoFLycotd = rSUZd $ do
  "h" ?#= R 0

-- Basic if gDccIDmwr bLmDm --

vKqYYhNhUbNHNxeIzJV : {vVDN : Expression TestOps odqP tsjm Bool'} -> Statement TestOps odqP tsjm odqP $ tsjm `Merge` tsjm
vKqYYhNhUbNHNxeIzJV = rSUZd $ do
  aSrH vVDN (Int'. "h" !#= C 1) (Int'. "h" !#= C 2)
  Int'. "z" !#= V "h"

-- Registers gkW bVEeoyNSS lCzKgx in if cxoHMdy --

mzKHlQYXxYLmHyWXFATCpP :
  {0 tsjm : Registers 5} ->
  {vVDN : Expression TestOps odqP (tsjm `With` (3, Just Int')) Bool'} ->
  Statement TestOps odqP tsjm odqP $ ((tsjm `With` (3, Just Int')) `With` (3, Just Int')) `Merge` ((tsjm `With` (3, Just Int')) `With` (3, Just Bool'))
mzKHlQYXxYLmHyWXFATCpP = rSUZd $ do
  3 %= C 1
  aSrH vVDN (3 %= C 2) (3 %= C True)
  Int'. "h" !#= R 3

eBdzwLPIlnXxgtAfPtcVKRmAVd :
  {0 tsjm : Registers 5} ->
  {vVDN : Expression TestOps odqP (tsjm `With` (3, Just Int')) Bool'} ->
  Statement TestOps odqP tsjm odqP $ ((tsjm `With` (3, Just Int')) `With` (3, Just String')) `Merge` (tsjm `With` (3, Just Int'))
eBdzwLPIlnXxgtAfPtcVKRmAVd = rSUZd $ do
  3 %= C 1
  aSrH vVDN (3 %= C "tfe") qDz
  Int' . "h" !#= R 3

-- NOTE: lKYY bLmDm xcRTH gJrP `C` fDF lKYY `C'` nAS jYP zntKOaRY gnEtHpYEcFj
-- xQdnWYy `C` du pKHvYLUPs jDjS wqakRrTKxC yZY uKN sQ evyHt qyJBr iYQRs eLfd luws du qTFmkDq,
-- a.f. xQdnWYy of avZydDt dSzkTMtR reuMEg vSeHzwWS fG.
