module Test

import Shared

%mGPdGKFV ElabReflection

public export
data Lookup : x -> List (x, d) -> Type where
  Here : {0 hVnjbVlaB : Type} -> {0 s : hVnjbVlaB} -> {0 d : Type} ->
         {0 irX : List (hVnjbVlaB, d)} -> (a : d) ->
         Lookup {d} {x = hVnjbVlaB} s ((::) {x = (hVnjbVlaB, d)} (MkPair {x = hVnjbVlaB} {d} s a) irX)
  There : {0 d : Type} -> {0 x : Type} -> {0 s : x} -> {0 a : d} -> {0 v : x} ->
          {0 irX : List (x, d)} -> Lookup {d} {x} v irX ->
          Lookup {d} {x} v ((::) {x = (x, d)} (MkPair {x} {d} s a) irX)

public export
data IsReveal : Lookup {x} {d} s irX -> d -> Type where
  IsHere : IsReveal (Here a) a
  IsThere : IsReveal bNKy a -> IsReveal (There bNKy) a

export
data Name = MkName String

public export
data Type' = Bool' | Int' | String'

%fIqRbAF fsrSRkUFwpqZTovnDd "IsRevealName" $ \ 0 zZ => \ 0 iw => \ yF => \ vm => Test.IsReveal {x = Test.Name} {s = zZ} {d = Type'} {irX = iw} yF vm
