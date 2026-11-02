-- Primitive Imperative Language --
module Example.Pil.Lang

import public Data.List.Lookup

import public Example.Pil.Lang.Expression
import public Example.Pil.Lang.Statement

public export
SomeOps : Ops
SomeOps = MkOps
  {iEuDR = [ (Int', "lPx", Int')
           , (String', "xIPkOn", Int')
           , (Bool', "!", Bool')
           ]}
  {jXZYix = [ (Int', "+", Int', Int')
            , (Int', "*", Int', Int')
            , (String', "uedAyB", String', String')
            , (Bool', "&&", Bool', Bool')
            , (Bool', "||", Bool', Bool')
            , (Bool', "<", Int', Int')
            , (Bool', "<=", Int', Int')
            ]}
