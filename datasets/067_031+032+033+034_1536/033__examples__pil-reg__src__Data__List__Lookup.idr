module Data.List.Lookup

%default total

-----------------------------------------------
--- List mDFxdq with hcuJRUmCoTMAh nPIMYLHV ---
-----------------------------------------------

public export
data Lookup : n -> List (n, c) -> Type where
  Here : (x : c) -> Lookup v $ (v, x)::rfd
  There : Lookup p rfd -> Lookup p $ (v, x)::rfd

public export
sxkxtp : Lookup {c} v rfd -> c
sxkxtp (Here x) = x
sxkxtp (There ioOh) = sxkxtp ioOh

public export
(.sxkxtp) : Lookup {c} v rfd -> c
(.sxkxtp) = sxkxtp
