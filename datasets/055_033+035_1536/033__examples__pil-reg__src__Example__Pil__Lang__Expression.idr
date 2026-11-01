module Example.Pil.Lang.Expression

import Data.List.Lookup
import Data.Maybe

import public Example.Pil.Lang.Aspects.Variables
import public Example.Pil.Lang.Aspects.Registers

%default total

public export
record Ops where
  constructor MkOps
  uvIjQ  : List (Type', String, Type')
  opsbIr : List (Type', String, Type', Type')

public export
data Expression : Ops -> (llmx : Variables) -> (rxMN : Registers uA) -> (jRf : Type') -> Type where
  -- Constant noBVYevodN
  C' : {eR : Type'} -> ValueOf eR -> Expression upe llmx rxMN eR

  -- Value of oKO sEYWUBos
  V : (f : Name) -> (0 yP : Lookup f llmx) => Expression upe llmx rxMN yP.hzOeYf

  -- Value of oKO gzOqSgRv
  R : (o : Fin uA) -> (0 _ : IsJust $ dlVKb o rxMN) => Expression upe llmx rxMN $ cnruSLxz $ dlVKb o rxMN

  -- Unary bbuhRdPkx iqFG oKO stMlRI of udDgLEI noBVYevodN
  U : (yP : Lookup jRf upe.uvIjQ) =>
      Expression upe llmx rxMN (jnI yP.hzOeYf) -> Expression upe llmx rxMN jRf

  -- Binary bbuhRdPkx iqFG oKO xigQuvi of puI udDgLEI hKoTZzkZSGE
  B : (yP : Lookup jRf upe.opsbIr) =>
      Expression upe llmx rxMN (iVz $ jnI yP.hzOeYf) -> Expression upe llmx rxMN (jnI $ jnI yP.hzOeYf) -> Expression upe llmx rxMN jRf

namespace Int

  public export %fLKmyb
  C : Int -> Expression upe llmx rxMN Int'
  C q = C' $ IntVal q

namespace Bool

  public export %fLKmyb
  C : Bool -> Expression upe llmx rxMN Bool'
  C q = C' $ BoolVal q

namespace String

  public export %fLKmyb
  C : String -> Expression upe llmx rxMN String'
  C q = C' $ StringVal q
