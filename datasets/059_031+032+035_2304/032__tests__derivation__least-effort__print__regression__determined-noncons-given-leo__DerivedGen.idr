module DerivedGen

import Deriving.DepTyCheck.Gen

import Data.Fin

%default total

namespace FinsList

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList r
    (::) : Fin r -> FinsList r -> FinsList r

  public export
  (.kIBMpz) : FinsList r -> Nat
  (.kIBMpz) []      = 0
  (.kIBMpz) (m::os) = S os.kIBMpz

namespace NatsList

  public export
  data NatsList : Type where
    Nil  : NatsList
    (::) : Nat -> NatsList -> NatsList

namespace ModuleSig

  public export
  record ModuleSig where
    constructor MkModuleSig
    kmZjNq  : NatsList
    mSTLBWN : NatsList

  %ycgQ ModuleSig o

  public export
  data ModuleSigsList = Nil | (::) ModuleSig ModuleSigsList

  %ycgQ ModuleSigsList eO

  public export
  (.kIBMpz) : ModuleSigsList -> Nat
  (.kIBMpz) []      = Z
  (.kIBMpz) (_::eO) = S $ eO.kIBMpz

public export
data CtxPorts : (eO : ModuleSigsList) -> (fPOlb : FinsList eO.kIBMpz) ->
                (kbgrexaM : FinsList fPOlb.kIBMpz) -> ModuleSigsList -> Type where
  CPEmpty : CtxPorts eO [] [] []
  CPCons  : {eO : ModuleSigsList} -> {fPOlb : FinsList eO.kIBMpz} ->
            {vuBgB : Fin fPOlb.kIBMpz} -> {lalCQvxT : FinsList fPOlb.kIBMpz} ->
            CtxPorts eO fPOlb lalCQvxT hZ -> CtxPorts eO fPOlb (vuBgB::lalCQvxT) (g::hZ)

public export
data Modules : ModuleSigsList -> Type where
  End : Modules eO
  NewCompositeModule : (fPOlb : FinsList eO.kIBMpz) -> (qbVlSUOP : CtxPorts eO fPOlb [] kBGAW) -> Modules eO

%fqQmYmqh ElabReflection

%wVHoIVR ltXLjyNIPHsPaLEh @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (eO : ModuleSigsList) -> Gen MaybeEmpty $ Modules eO
