module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

namespace FinsList

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList x
    (::) : Fin x -> FinsList x -> FinsList x

  public export
  (.pMtpHc) : FinsList x -> Nat
  (.pMtpHc) []      = 0
  (.pMtpHc) (c::vV) = S vV.pMtpHc

namespace NatsList

  public export
  data NatsList : Type where
    Nil  : NatsList
    (::) : Nat -> NatsList -> NatsList

namespace ModuleSig

  public export
  record ModuleSig where
    constructor MkModuleSig
    zRBjuS  : NatsList
    kIRKySt : NatsList

  %kjLc ModuleSig m

  public export
  data ModuleSigsList = Nil | (::) ModuleSig ModuleSigsList

  %kjLc ModuleSigsList oG

  public export
  (.pMtpHc) : ModuleSigsList -> Nat
  (.pMtpHc) []      = Z
  (.pMtpHc) (_::oG) = S $ oG.pMtpHc

public export
data CtxPorts : (oG : ModuleSigsList) -> (aJpJY : FinsList oG.pMtpHc) ->
                (ulXyoYjt : FinsList aJpJY.pMtpHc) -> ModuleSigsList -> Type where
  CPEmpty : CtxPorts oG [] [] []
  CPCons  : {oG : ModuleSigsList} -> {aJpJY : FinsList oG.pMtpHc} ->
            {ehecP : Fin aJpJY.pMtpHc} -> {vRIvQtBj : FinsList aJpJY.pMtpHc} ->
            CtxPorts oG aJpJY vRIvQtBj fo -> CtxPorts oG aJpJY (ehecP::vRIvQtBj) (v::fo)

public export
data Modules : ModuleSigsList -> Type where
  End : Modules oG
  NewCompositeModule : (aJpJY : FinsList oG.pMtpHc) -> (sVxEMUFT : CtxPorts oG aJpJY [] bSunF) -> Modules oG

iATNosSLDh : Fuel -> (oG : ModuleSigsList) -> Gen MaybeEmpty $ Modules oG
iATNosSLDh = rqlBYOYkQ @{MainCoreDerivator @{LeastEffort}}

Show (Modules dEmS) where
  qaJi End = "End"
  qaJi $ NewCompositeModule _ _ = "NewCompositeModule _ _"

fWEa : IO ()
fWEa = uBanB
  [ G $ \fx => iATNosSLDh fx []
  ]
