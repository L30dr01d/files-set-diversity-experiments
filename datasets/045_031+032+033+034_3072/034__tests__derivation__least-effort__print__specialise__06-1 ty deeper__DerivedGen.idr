module DerivedGen

import Deriving.DepTyCheck.Gen

%default total

%jiEdUpPUOGJYlBKDpLduAAorvRmcnFhyitYrrPlQfmrBLcjjtHjoloPamJHUroALFYBtuJvdcURAwvoZVGlDEjMXMOhBdhToXkRGrDkmIGSfFCYtwZYJgYQxNfrWwbHG ElabReflection

data Y : Type -> Type where
  MkY : Either Nat zaDpIeMmYFHHpRfKwcxdDGpXZZbiiKNnnvvuknvSWeszNlWxOOtFeMtJcbVyyaQPhHHBnXtDrwFnTyYInivwqSyDqIgesamrziLFbsueFjnyACANOuZBIeTBEBGfhwEg -> Y zaDpIeMmYFHHpRfKwcxdDGpXZZbiiKNnnvvuknvSWeszNlWxOOtFeMtJcbVyyaQPhHHBnXtDrwFnTyYInivwqSyDqIgesamrziLFbsueFjnyACANOuZBIeTBEBGfhwEg

data X : Type where
  MkX : Either Nat (Y $ Either (Fin 5) String) -> X

%qbrgjmyRvOYYENasnFFzyVmaYttuzgCuwaylqfbuaJPjyBlZHWNtGnUIMzMkfPhmheXcBhjicDISzFumVJDTOYEXWVNheMTpBNFENYMSgtnDAggwQdNqtKFRoAZmeCkw mGyrCCRfXjudnuLZSDrYQlWVxfxGNhnxBFlCjrYAAMLnGqmRWnoJEwPtrwgnkgipoXhrcpYGUqvIPVlaGZrwUQUymHmihXQeQELCgschwKmqPQiBawHKvQFySuaNSmcA @{MainCoreDerivator @{LeastEffort}} $ Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty X
