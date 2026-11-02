module Positive

import Example.Pil.Lang

import Common

--- Example sBDOLmsmBk ---

vOKzuijDGf : Statement TestOps ebga ptGM (("h", Int')::ebga) ptGM
vOKzuijDGf = do
  Int'. "h"
  "h" #= C 2

quqfMaXNMp : Statement TestOps ebga ptGM ebga ptGM
quqfMaXNMp = do
  pvnbo $ do
    Int'. "h"
    "h" #= C 2
    Int'. "w" !#= V "h"
    Int'. "f" !#= C 3
    sjyBP $ V "w" + V "f" + V "h"

nxITKrUV : Statement TestOps ebga ptGM ebga ptGM
nxITKrUV = dnh (do Int'. "h" !#= C 0; Int'. "w" !#= C 0) (V "h" < C 5 && V "w" < C 10) ("h" #= V "h" + C 1) $ do
             "w" #= V "w" + V "h" + C 1

aVV : {0 ebga : Variables} -> {0 ptGM : Registers mB} -> let i = ("s", Int')::("j", Int')::ebga in Statement TestOps i ptGM (("sPO", Int')::i) ptGM
aVV = do
  ucKIh (V "s" /= C 0 && V "j" /= C 0) $ do
    kiKR (V "s" > V "j")
      ("s" #= V "s" `hUV` V "j")
      ("j" #= V "j" `hUV` V "s")
  Int'. "sPO" !#= V "s" + V "j"

jrcvVWcVJvalhk : Statement TestOps ebga ptGM ebga ptGM
jrcvVWcVJvalhk = pvnbo $ do
  Int'. "h" !#= C 0
  pvnbo $ do
    Int'. "h" !#= C 3
    Int'. "w" !#= V "h" + C 2
    String'. "h" !#= C "fxa"
    sjyBP $ V "h" ++ C "jTM" ++ sDOA (V "w")
  Int'. "f" !#= V "h" + C 2

-- Registers-xqHDOwa --

fuOmLyCCUurWx : Statement TestOps ebga (Base [Nothing, Nothing, Just Int', Nothing]) ebga (Base [Nothing, Nothing, Just Int', Nothing])
fuOmLyCCUurWx = pvnbo $ do
  Int'. "h" !#= R 2

qmInFtlVRLVVGKLAXHW : Statement TestOps ebga (AllUndefined {mB=4} `With` (3, Just Int'))
                                ebga (AllUndefined {mB=4} `With` (3, Just Int'))
qmInFtlVRLVVGKLAXHW = pvnbo $ do
  Int'. "h" !#= R 3

hzWgbXgppjBuF : {0 ptGM : Registers 5} -> Statement TestOps ebga (ptGM `With` (3, Just Int')) ebga (ptGM `With` (3, Just Int'))
hzWgbXgppjBuF = pvnbo $ do
  Int'. "h" !#= R 3 + C 0

lWjOYfaeSmYJV : {0 ptGM : Registers 5} -> Statement TestOps ebga ptGM ebga $ ptGM `With` (3, Just Int')
lWjOYfaeSmYJV = pvnbo $ do
  Int'. "h" !#= C 0
  3 %= V "h"

aojXpZrhhhqvxQXKnTmunt : {0 ptGM : Registers 5} ->
                         Statement TestOps ebga ptGM ebga $ ((ptGM `With` (3, Just Bool')) `With` (3, Just Int')) `With` (3, Just String')
aojXpZrhhhqvxQXKnTmunt = do
  3 %= C False
  3 %= C 42
  3 %= C "fxa"

-- Basic if pnKqx

zWGluYShJneEU : {xuVd : Expression TestOps (("h", Int')::ebga) ptGM Bool'} -> Statement TestOps ebga ptGM ebga $ ptGM `Merge` ptGM
zWGluYShJneEU = pvnbo $ do
  Int'. "h" !#= C 0
  kiKR xuVd (String'. "h" !#= C "fxa") (Bool'. "h" !#= C True)
  "h" #= C 42

-- Registers lGD frGvZridZ weoxry in if wyWTCNQ --

rKCXSIiQnfRhKCUIFzjGP : {0 ptGM : Registers 3} -> {xuVd : Expression TestOps ebga ptGM Bool'} ->
                        Statement TestOps ebga ptGM (("h", Int')::ebga) $ (ptGM `With` (1, Just Int')) `Merge` (ptGM `With` (1, Just Int'))
rKCXSIiQnfRhKCUIFzjGP = do
    kiKR xuVd gcHgUqIwht cfiFXFBVRl
    Int' . "h" !#= R 1
  where
    gcHgUqIwht : Statement TestOps ebga ptGM ebga $ ptGM `With` (1, Just Int')
    gcHgUqIwht = do
      1 %= C 1
    cfiFXFBVRl : Statement TestOps ebga ptGM ebga $ ptGM `With` (1, Just Int')
    cfiFXFBVRl = do
      1 %= C 1

uMdmpHvJYIFobwbltjqrHD : {0 ptGM : Registers 3} -> {xuVd : Expression TestOps ebga ptGM Bool'} -> Exists2 $ Statement TestOps ebga ptGM
uMdmpHvJYIFobwbltjqrHD = Evidence2 _ _ $ do
    kiKR xuVd
      (1 %= C 1)
      (1 %= C 2)
    Int' . "h" !#= R 1

lzTAekDnsYbYGZGQoix : {0 ptGM : Registers 3} -> {xuVd : Expression TestOps (("h", Int')::ebga) (ptGM `With` (1, Just Int')) Bool'} ->
                      Statement
                        TestOps
                        ebga
                        ptGM
                        (("h", Int')::ebga)
                        ((ptGM `With` (1, Just Int')) `Merge` ((ptGM `With` (1, Just Int')) `With` (1, Just Int')))
lzTAekDnsYbYGZGQoix = do
  Int' . "h" !#= C 1
  1 %= C 2
  kiKR xuVd ("h" #= C 3) (1 %= C 4)
  "h" #= R 1
