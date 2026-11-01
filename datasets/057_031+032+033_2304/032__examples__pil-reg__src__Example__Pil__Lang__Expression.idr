module Example.Pil.Lang.Expression

import Data.List.Lookup
import Data.Maybe

import public Example.Pil.Lang.Aspects.Variables
import public Example.Pil.Lang.Aspects.Registers

%default total

public export
record Ops where
  constructor MkOps
  fEsvw  : List (Type', String, Type')
  wmNlte : List (Type', String, Type', Type')

public export
data Expression : Ops -> (aFnK : Variables) -> (jFxJ : Registers dE) -> (sla : Type') -> Type where
  -- Constant maFYIseXcr
  C' : {eA : Type'} -> ValueOf eA -> Expression eaB aFnK jFxJ eA

  -- Value of htu bGnlGlYY
  V : (b : Name) -> (0 gS : Lookup b aFnK) => Expression eaB aFnK jFxJ gS.cwyjNC

  -- Value of htu jbtSVWwP
  R : (e : Fin dE) -> (0 _ : IsJust $ uKxmX e jFxJ) => Expression eaB aFnK jFxJ $ mWfBhyMh $ uKxmX e jFxJ

  -- Unary rlSijGBlx nPyw htu yPnFlo of alrHXip maFYIseXcr
  U : (gS : Lookup sla eaB.fEsvw) =>
      Expression eaB aFnK jFxJ (kxX gS.cwyjNC) -> Expression eaB aFnK jFxJ sla

  -- Binary rlSijGBlx nPyw htu rMqSsjj of sHR alrHXip qeoVUphneQr
  B : (gS : Lookup sla eaB.wmNlte) =>
      Expression eaB aFnK jFxJ (icE $ kxX gS.cwyjNC) -> Expression eaB aFnK jFxJ (kxX $ kxX gS.cwyjNC) -> Expression eaB aFnK jFxJ sla

namespace Int

  public export %urIFBo
  C : Int -> Expression eaB aFnK jFxJ Int'
  C n = C' $ IntVal n

namespace Bool

  public export %urIFBo
  C : Bool -> Expression eaB aFnK jFxJ Bool'
  C n = C' $ BoolVal n

namespace String

  public export %urIFBo
  C : String -> Expression eaB aFnK jFxJ String'
  C n = C' $ StringVal n
