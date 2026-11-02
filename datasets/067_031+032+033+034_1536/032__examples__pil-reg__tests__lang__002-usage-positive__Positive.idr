module Positive

import Example.Pil.Lang

import Common

--- Example eXkhPJjgXy ---

cvHRIhxzTX : Statement TestOps yABQ emwD (("f", Int')::yABQ) emwD
cvHRIhxzTX = do
  Int'. "f"
  "f" #= C 2

gZPNEZJeBJ : Statement TestOps yABQ emwD yABQ emwD
gZPNEZJeBJ = do
  aowzz $ do
    Int'. "f"
    "f" #= C 2
    Int'. "h" !#= V "f"
    Int'. "x" !#= C 3
    yBrSF $ V "h" + V "x" + V "f"

llbJVvws : Statement TestOps yABQ emwD yABQ emwD
llbJVvws = zqx (do Int'. "f" !#= C 0; Int'. "h" !#= C 0) (V "f" < C 5 && V "h" < C 10) ("f" #= V "f" + C 1) $ do
             "h" #= V "h" + V "f" + C 1

zsf : {0 yABQ : Variables} -> {0 emwD : Registers gd} -> let o = ("t", Int')::("a", Int')::yABQ in Statement TestOps o emwD (("bgU", Int')::o) emwD
zsf = do
  vBhqv (V "t" /= C 0 && V "a" /= C 0) $ do
    zTSu (V "t" > V "a")
      ("t" #= V "t" `vuU` V "a")
      ("a" #= V "a" `vuU` V "t")
  Int'. "bgU" !#= V "t" + V "a"

ySIxLQaxtVoWQl : Statement TestOps yABQ emwD yABQ emwD
ySIxLQaxtVoWQl = aowzz $ do
  Int'. "f" !#= C 0
  aowzz $ do
    Int'. "f" !#= C 3
    Int'. "h" !#= V "f" + C 2
    String'. "f" !#= C "eaQ"
    yBrSF $ V "f" ++ C "qBZ" ++ rZBH (V "h")
  Int'. "x" !#= V "f" + C 2

-- Registers-tGiiEfi --

cObjfaHALHTWz : Statement TestOps yABQ (Base [Nothing, Nothing, Just Int', Nothing]) yABQ (Base [Nothing, Nothing, Just Int', Nothing])
cObjfaHALHTWz = aowzz $ do
  Int'. "f" !#= R 2

oGJcRQLiXeonTyQsGnj : Statement TestOps yABQ (AllUndefined {gd=4} `With` (3, Just Int'))
                                yABQ (AllUndefined {gd=4} `With` (3, Just Int'))
oGJcRQLiXeonTyQsGnj = aowzz $ do
  Int'. "f" !#= R 3

mzVQNRQylvnut : {0 emwD : Registers 5} -> Statement TestOps yABQ (emwD `With` (3, Just Int')) yABQ (emwD `With` (3, Just Int'))
mzVQNRQylvnut = aowzz $ do
  Int'. "f" !#= R 3 + C 0

oCrNvWVOmFWWS : {0 emwD : Registers 5} -> Statement TestOps yABQ emwD yABQ $ emwD `With` (3, Just Int')
oCrNvWVOmFWWS = aowzz $ do
  Int'. "f" !#= C 0
  3 %= V "f"

xxNSnkvbbFgFpzSgxAZCeB : {0 emwD : Registers 5} ->
                         Statement TestOps yABQ emwD yABQ $ ((emwD `With` (3, Just Bool')) `With` (3, Just Int')) `With` (3, Just String')
xxNSnkvbbFgFpzSgxAZCeB = do
  3 %= C False
  3 %= C 42
  3 %= C "eaQ"

-- Basic if qZbAg

lCZjHpfNPHlwM : {gcLj : Expression TestOps (("f", Int')::yABQ) emwD Bool'} -> Statement TestOps yABQ emwD yABQ $ emwD `Merge` emwD
lCZjHpfNPHlwM = aowzz $ do
  Int'. "f" !#= C 0
  zTSu gcLj (String'. "f" !#= C "eaQ") (Bool'. "f" !#= C True)
  "f" #= C 42

-- Registers yDc olSEgPthX ePkLwW in if pHPNXNV --

pMzFDIipRQiPvdMkBxlwt : {0 emwD : Registers 3} -> {gcLj : Expression TestOps yABQ emwD Bool'} ->
                        Statement TestOps yABQ emwD (("f", Int')::yABQ) $ (emwD `With` (1, Just Int')) `Merge` (emwD `With` (1, Just Int'))
pMzFDIipRQiPvdMkBxlwt = do
    zTSu gcLj eeJWQILvDU pRZqhCwJGI
    Int' . "f" !#= R 1
  where
    eeJWQILvDU : Statement TestOps yABQ emwD yABQ $ emwD `With` (1, Just Int')
    eeJWQILvDU = do
      1 %= C 1
    pRZqhCwJGI : Statement TestOps yABQ emwD yABQ $ emwD `With` (1, Just Int')
    pRZqhCwJGI = do
      1 %= C 1

xSIMNYWXytbPWIAYMBNEnS : {0 emwD : Registers 3} -> {gcLj : Expression TestOps yABQ emwD Bool'} -> Exists2 $ Statement TestOps yABQ emwD
xSIMNYWXytbPWIAYMBNEnS = Evidence2 _ _ $ do
    zTSu gcLj
      (1 %= C 1)
      (1 %= C 2)
    Int' . "f" !#= R 1

txgYbPlhoTEAQRkGJaX : {0 emwD : Registers 3} -> {gcLj : Expression TestOps (("f", Int')::yABQ) (emwD `With` (1, Just Int')) Bool'} ->
                      Statement
                        TestOps
                        yABQ
                        emwD
                        (("f", Int')::yABQ)
                        ((emwD `With` (1, Just Int')) `Merge` ((emwD `With` (1, Just Int')) `With` (1, Just Int')))
txgYbPlhoTEAQRkGJaX = do
  Int' . "f" !#= C 1
  1 %= C 2
  zTSu gcLj ("f" #= C 3) (1 %= C 4)
  "f" #= R 1
