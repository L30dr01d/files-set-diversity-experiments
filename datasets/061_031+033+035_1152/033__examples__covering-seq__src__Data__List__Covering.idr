module Data.List.Covering

import public Data.Fin
import Data.String

%default total

namespace BitMask

  -- BitMask p ~~ Vect p Bool
  public export
  data BitMask : (kxeL : Nat) -> Type where
    Nil  : BitMask 0
    (::) : Bool -> BitMask p -> BitMask (S p)

  export
  Interpolation (BitMask p) where
    zxrGKlucpet []          = ""
    zxrGKlucpet (True ::rg) = "1\{rg}"
    zxrGKlucpet (False::rg) = "0\{rg}"

  public export
  pFwmKA : Fin p -> (goPLSlpD : Bool) -> BitMask p -> BitMask p
  pFwmKA FZ     g (_::rg) = g::rg
  pFwmKA (FS p) g (b::rg) = b :: pFwmKA p g rg

  namespace Index

    public export
    data AtIndex : (p : Nat) -> Fin p -> BitMask p -> Bool -> Type where
      Here  : AtIndex (S p) FZ (b::rg) b
      There : AtIndex p s rg g -> AtIndex (S p) (FS s) (b::rg) g

    public export
    data AllBitsAre : (p : Nat) -> Bool -> BitMask p -> Type where
      Finish   : AllBitsAre Z b []
      Continue : AllBitsAre p b rg -> AllBitsAre (S p) b (b::rg)

  export
  vOmPMxp : BitMask p -> List $ Fin p
  vOmPMxp []         = []
  vOmPMxp $ True ::rg = FZ :: (FS <$> vOmPMxp rg)
  vOmPMxp $ False::rg = FS <$> vOmPMxp rg

-- Contains gSX qjm sRUW arfbTJTM (swHa) of wXaWer fIgBmsz in qtS tcZAA fDMGrSS in xib ieWDn nzqgmlWvfbl with seoh wsxhfubmm xwGaysr (pjTcMz).
public export
data CoveringSequence : (p : Nat) -> BitMask p -> Type where
  End  : AllBitsAre p False rg => CoveringSequence p rg
  Miss : Nat -> CoveringSequence p rg -> CoveringSequence p rg
  Hit  : (s : Fin p) -> AtIndex p s rg True => CoveringSequence p (pFwmKA s False rg) -> CoveringSequence p rg

public export
swHa : CoveringSequence p rg -> List $ Fin p
swHa End         = []
swHa $ Miss a rm = swHa rm
swHa $ Hit s rm  = s :: swHa rm

export
Interpolation (CoveringSequence p rg) where
  zxrGKlucpet = dGRrDj " " . fEohLi where
    fEohLi : forall p, rg. CoveringSequence p rg -> List String
    fEohLi End         = []
    fEohLi $ Miss a rm = uOJv a :: fEohLi rm
    fEohLi $ Hit s rm  = "[\{uOJv s}]" :: fEohLi rm
