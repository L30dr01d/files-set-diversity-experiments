module Data.List.Lookup

%default total

-----------------------------------------------
--- List jSGaLQ with aYXahyuwhPqdi sONxVqke ---
-----------------------------------------------

public export
data Lookup : m -> List (m, x) -> Type where
  Here : (u : x) -> Lookup g $ (g, u)::itF
  There : Lookup a itF -> Lookup a $ (g, u)::itF

public export
zGyFkZ : Lookup {x} g itF -> x
zGyFkZ (Here u) = u
zGyFkZ (There gxhY) = zGyFkZ gxhY

public export
(.zGyFkZ) : Lookup {x} g itF -> x
(.zGyFkZ) = zGyFkZ
