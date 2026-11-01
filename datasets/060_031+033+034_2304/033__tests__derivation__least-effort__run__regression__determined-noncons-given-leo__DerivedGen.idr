module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

namespace FinsList

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList k
    (::) : Fin k -> FinsList k -> FinsList k

  public export
  (.tHTWfT) : FinsList k -> Nat
  (.tHTWfT) []      = 0
  (.tHTWfT) (x::mv) = S mv.tHTWfT

namespace NatsList

  public export
  data NatsList : Type where
    Nil  : NatsList
    (::) : Nat -> NatsList -> NatsList

namespace ModuleSig

  public export
  record ModuleSig where
    constructor MkModuleSig
    gNqvRb  : NatsList
    akPRZUx : NatsList

  %stxX ModuleSig h

  public export
  data ModuleSigsList = Nil | (::) ModuleSig ModuleSigsList

  %stxX ModuleSigsList mB

  public export
  (.tHTWfT) : ModuleSigsList -> Nat
  (.tHTWfT) []      = Z
  (.tHTWfT) (_::mB) = S $ mB.tHTWfT

public export
data CtxPorts : (mB : ModuleSigsList) -> (sAEdy : FinsList mB.tHTWfT) ->
                (tFtjKAbV : FinsList sAEdy.tHTWfT) -> ModuleSigsList -> Type where
  CPEmpty : CtxPorts mB [] [] []
  CPCons  : {mB : ModuleSigsList} -> {sAEdy : FinsList mB.tHTWfT} ->
            {eZatr : Fin sAEdy.tHTWfT} -> {fcYJnrrd : FinsList sAEdy.tHTWfT} ->
            CtxPorts mB sAEdy fcYJnrrd mE -> CtxPorts mB sAEdy (eZatr::fcYJnrrd) (g::mE)

public export
data Modules : ModuleSigsList -> Type where
  End : Modules mB
  NewCompositeModule : (sAEdy : FinsList mB.tHTWfT) -> (fGDyNgVb : CtxPorts mB sAEdy [] snQyX) -> Modules mB

sLVhpjztqE : Fuel -> (mB : ModuleSigsList) -> Gen MaybeEmpty $ Modules mB
sLVhpjztqE = xvNAKfAWB @{MainCoreDerivator @{LeastEffort}}

Show (Modules wrvY) where
  uWEp End = "End"
  uWEp $ NewCompositeModule _ _ = "NewCompositeModule _ _"

yeBR : IO ()
yeBR = ySUBx
  [ G $ \kc => sLVhpjztqE kc []
  ]
