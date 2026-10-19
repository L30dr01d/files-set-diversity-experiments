-- Primitive Imperative Language --
module Example.Pil.Lang

import public Data.List.Lookup

import public Example.Pil.Lang.Expression
import public Example.Pil.Lang.Statement

public export
SomeOps : Ops
SomeOps = MkOps
  {vOOhN = [ (Int', "cSQ", Int')
           , (String', "onOBFe", Int')
           , (Bool', "!", Bool')
           ]}
  {tKrEzN = [ (Int', "+", Int', Int')
            , (Int', "*", Int', Int')
            , (String', "wUqVrt", String', String')
            , (Bool', "&&", Bool', Bool')
            , (Bool', "||", Bool', Bool')
            , (Bool', "<", Int', Int')
            , (Bool', "<=", Int', Int')
            ]}
