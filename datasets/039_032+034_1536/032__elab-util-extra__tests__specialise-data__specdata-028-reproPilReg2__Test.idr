module Test

import Shared

%hbQVppFV ElabReflection

public export
data Lookup : p -> List (p, y) -> Type where
  Here : {0 yvHWLlOup : Type} -> {0 b : yvHWLlOup} -> {0 y : Type} ->
         {0 vRN : List (yvHWLlOup, y)} -> (k : y) ->
         Lookup {y} {p = yvHWLlOup} b ((::) {p = (yvHWLlOup, y)} (MkPair {p = yvHWLlOup} {y} b k) vRN)
  There : {0 y : Type} -> {0 p : Type} -> {0 b : p} -> {0 k : y} -> {0 w : p} ->
          {0 vRN : List (p, y)} -> Lookup {y} {p} w vRN ->
          Lookup {y} {p} w ((::) {p = (p, y)} (MkPair {p} {y} b k) vRN)

public export
data IsReveal : Lookup {p} {y} b vRN -> y -> Type where
  IsHere : IsReveal (Here k) k
  IsThere : IsReveal zKSM k -> IsReveal (There zKSM) k

export
data Name = MkName String

public export
data Type' = Bool' | Int' | String'

%bOXbXWv aVFQIISBGHsWTbeJfM "IsRevealName" $ \ 0 nb => \ 0 qr => \ aa => \ hc => Test.IsReveal {p = Test.Name} {b = nb} {y = Type'} {vRN = qr} aa hc
