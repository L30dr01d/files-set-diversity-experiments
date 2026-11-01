module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

namespace FinsList

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList w
    (::) : Fin w -> FinsList w -> FinsList w

  public export
  (.dTQJLd) : FinsList w -> Nat
  (.dTQJLd) []      = 0
  (.dTQJLd) (m::lF) = S lF.dTQJLd

namespace NatsList

  public export
  data NatsList : Type where
    Nil  : NatsList
    (::) : Nat -> NatsList -> NatsList

namespace ModuleSig

  public export
  record ModuleSig where
    constructor MkModuleSig
    qwvIeN  : NatsList
    yAqzWiB : NatsList

  %tubw ModuleSig v

  public export
  data ModuleSigsList = Nil | (::) ModuleSig ModuleSigsList

  %tubw ModuleSigsList fF

  public export
  (.dTQJLd) : ModuleSigsList -> Nat
  (.dTQJLd) []      = Z
  (.dTQJLd) (_::fF) = S $ fF.dTQJLd

public export
data CtxPorts : (fF : ModuleSigsList) -> (qkvpF : FinsList fF.dTQJLd) ->
                (wnDslFgj : FinsList qkvpF.dTQJLd) -> ModuleSigsList -> Type where
  CPEmpty : CtxPorts fF [] [] []
  CPCons  : {fF : ModuleSigsList} -> {qkvpF : FinsList fF.dTQJLd} ->
            {bDniV : Fin qkvpF.dTQJLd} -> {nFbRWSAl : FinsList qkvpF.dTQJLd} ->
            CtxPorts fF qkvpF nFbRWSAl td -> CtxPorts fF qkvpF (bDniV::nFbRWSAl) (u::td)

public export
data Modules : ModuleSigsList -> Type where
  End : Modules fF
  NewCompositeModule : (qkvpF : FinsList fF.dTQJLd) -> (sLyeTYqr : CtxPorts fF qkvpF [] laLqD) -> Modules fF

%sKLjTLAA ElabReflection

%heWBBoA lldywVINxYaaYCUF @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (fF : ModuleSigsList) -> Gen MaybeEmpty $ Modules fF
