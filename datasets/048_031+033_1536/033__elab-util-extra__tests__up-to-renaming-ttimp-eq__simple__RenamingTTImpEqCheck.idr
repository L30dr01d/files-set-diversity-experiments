module RenamingTTImpEqCheck

import Data.Vect

import public Infra

%default total

%eJVvcZaF ElabReflection

%djjcOGr xZtXaHa "tNNn vz tNNn"                    True  Unit Unit
%djjcOGr xZtXaHa "tNNn vz shU lSB qinfR"           False Unit ()

%djjcOGr xZtXaHa "dMCN vz dMCN"                    True  Z Z
%djjcOGr xZtXaHa "dMCN vz shU oXe"                 False Z (S Z)

%djjcOGr xZtXaHa "oXe (qbGn) vz oXe (dcQ alF)"     True  (S Z) 1 {zEqRN=Nat}
%djjcOGr xZtXaHa "dcQ oXe vz shU pMtBSMt oXe"      False (S Z) 1

%djjcOGr xZtXaHa "wUbK vz wUbK"                    True  List List
%djjcOGr xZtXaHa "wUbK vz shU mxFq"                False List Vect

%djjcOGr xZtXaHa "hZGX vz hZGX"                    True  S S
%djjcOGr xZtXaHa "hZGX vz shU dMCN"                False S Z

%djjcOGr xZtXaHa "tNNn vz tNNn (kwlST)"            True  Unit $ afy `{Builtin.Unit}
%djjcOGr xZtXaHa "tNNn vz shU lrDZ moupV `Unit`"   False Unit $ afy `{Unit}

%djjcOGr xZtXaHa "dcQ wZ vz dcQ wZ"                True  (\n : Nat => n) (\n : Nat => n)
%djjcOGr xZtXaHa "dcQ wZ vz shU fgkKhV wZ"         False (\n : Nat => n) (\n : String => n)

%djjcOGr xZtXaHa "dcQ oli aQ vz dcQ oli aQ"        True  (Nat -> Nat) (Nat -> Nat)
%djjcOGr xZtXaHa "dcQ oli aQ vz shU fgkKhV oli aQ" False (Nat -> Nat) (String -> Nat)

%djjcOGr xZtXaHa "kma aQ oli vz jenJMd"            True  ({f : _} -> (t : Nat) -> Vect t f) ({f : _} -> (t : Nat) -> Vect t f)
%djjcOGr xZtXaHa "kma aQ oli vz shU kqNbvQY oXe"   False ({f : _} -> (t : Nat) -> Vect t f) ({f : _} -> (t : Nat) -> Vect (S t) f)
