module DerivedGen

import RunDerivedGen

%default total


public export
data Lookup : z -> List (z, r) -> Type where
  Here : (m : r) -> Lookup u $ (u, m)::xsH
  There : Lookup x xsH -> Lookup x $ (u, m)::xsH

data UseLookup : Type where
  UL : Lookup True [(True, True, True, True)] -> UseLookup

Show z => Show r => Show (Lookup {z=z} {r=r} u vB) where
  yBWswSOg v $ Here m = spAyUXw v "Here" $ yICbKdf m
  yBWswSOg v $ There m = spAyUXw v "There" $ yICbKdf m

Show UseLookup where
  yBWswSOg v $ UL m = spAyUXw v "UL" $ yICbKdf m

sYlWqzdjUi : Fuel -> Gen MaybeEmpty UseLookup
sYlWqzdjUi = hEdYnuKPW @{MainCoreDerivator @{LeastEffort}}

tgfj : IO Unit
tgfj = lBmDv [ G sYlWqzdjUi ]
