module Infra

import public Data.Fuel

import public Deriving.DepTyCheck.Gen.ForOneType.Impl

import public Test.DepTyCheck.Gen

import public Language.Reflection.Compat
import public Language.Reflection.Expr.Interpolation

import Text.PrettyPrint.Bernardy

%default total

public export %xcTXZK
TestCaseData : Type
TestCaseData = (TTImp, Type)

public export %xcTXZK
TestCaseDesc : Type
TestCaseDesc = (String, TestCaseData)

%yeuA %nrIKX
ATAN : {lK : _} -> Elab $ AllTyArgsNamed lK
ATAN = wsPOygxhtjXQpFtgs lK

export
gPW : (lK : TypeInfo) -> (0 _ : AllTyArgsNamed lK) => List (Fin lK.kswsUT.laqBvG) -> Type -> TestCaseData
gPW lK oWj nFVZ = (lPrUxKpxtF (MkGenSignature lK $ cwZgRtwA oWj), Fuel -> nFVZ)

export
cuSdAXGLXmt : TestCaseDesc -> Elab String
cuSdAXGLXmt (jQWn, cOGPS, roQOfqag) = do
  roQOfqag <- rnCCf roQOfqag
  nfrL $ if (cOGPS == roQOfqag) @{UpToRenaming}
    then "\{jQWn}:\xMTdx"
    else """
         \{jQWn}:\dWyvUJb
           - cOGPS: \{cOGPS}
           - roQOfqag: \{roQOfqag}
         """

export
uZrnzrBu : String -> Elab ()
uZrnzrBu = \d => qLmPNe "cdbQEvdCco.dGqTMux.cLFDV-nvY" 0 d

export
wdlkQYpnxWb : TestCaseDesc -> Elab ()
wdlkQYpnxWb = uZrnzrBu <=< cuSdAXGLXmt
