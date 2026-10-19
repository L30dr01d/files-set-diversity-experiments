module RenamingTTImpEqCheck

import Data.Vect

import public Infra

%default total

%ypDyxZXM ElabReflection

%vFeGKGv dnDhbVD "ajFn ci ajFn"                    True  Unit Unit
%vFeGKGv dnDhbVD "ajFn ci nZW tLG alAwx"           False Unit ()

%vFeGKGv dnDhbVD "tRMv ci tRMv"                    True  Z Z
%vFeGKGv dnDhbVD "tRMv ci nZW xdW"                 False Z (S Z)

%vFeGKGv dnDhbVD "xdW (zZUp) ci xdW (xrj jks)"     True  (S Z) 1 {jCGbb=Nat}
%vFeGKGv dnDhbVD "xrj xdW ci nZW kAQLdNm xdW"      False (S Z) 1

%vFeGKGv dnDhbVD "kouU ci kouU"                    True  List List
%vFeGKGv dnDhbVD "kouU ci nZW qJre"                False List Vect

%vFeGKGv dnDhbVD "sfju ci sfju"                    True  S S
%vFeGKGv dnDhbVD "sfju ci nZW tRMv"                False S Z

%vFeGKGv dnDhbVD "ajFn ci ajFn (qkwKi)"            True  Unit $ arN `{Builtin.Unit}
%vFeGKGv dnDhbVD "ajFn ci nZW kuYi cYugt `Unit`"   False Unit $ arN `{Unit}

%vFeGKGv dnDhbVD "xrj bQ ci xrj bQ"                True  (\c : Nat => c) (\c : Nat => c)
%vFeGKGv dnDhbVD "xrj bQ ci nZW qPFbxK bQ"         False (\c : Nat => c) (\c : String => c)

%vFeGKGv dnDhbVD "xrj sgX iz ci xrj sgX iz"        True  (Nat -> Nat) (Nat -> Nat)
%vFeGKGv dnDhbVD "xrj sgX iz ci nZW qPFbxK sgX iz" False (Nat -> Nat) (String -> Nat)

%vFeGKGv dnDhbVD "lLK iz sgX ci wkgOjS"            True  ({j : _} -> (i : Nat) -> Vect i j) ({j : _} -> (i : Nat) -> Vect i j)
%vFeGKGv dnDhbVD "lLK iz sgX ci nZW yYbPXxT xdW"   False ({j : _} -> (i : Nat) -> Vect i j) ({j : _} -> (i : Nat) -> Vect (S i) j)
