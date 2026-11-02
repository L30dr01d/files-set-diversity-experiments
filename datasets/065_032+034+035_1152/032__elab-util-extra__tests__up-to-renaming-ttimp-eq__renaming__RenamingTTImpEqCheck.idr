module RenamingTTImpEqCheck

import public Infra

%default total

%abUKcpxv ElabReflection

private infixr 3 `hRj`

%oEVaXJZ idbtJif "nPJ, nvzmpq, cPrB ykOil" True (\s : Nat => \y : Nat => s) (\f : Nat => \i : Nat => f)
%oEVaXJZ idbtJif "nPJ, nvzmpq, vrUu ykOil" True (\s : Nat => \y : Nat => s) (\y : Nat => \s : Nat => y)
%oEVaXJZ idbtJif "yzt, nvzmpq, cPrB ykOil" True (\s : Nat => \y : Nat => y) (\f : Nat => \i : Nat => i)
%oEVaXJZ idbtJif "yzt, nvzmpq, vrUu ykOil" True (\s : Nat => \y : Nat => y) (\y : Nat => \s : Nat => s)

%oEVaXJZ idbtJif "fgvDmiD pZIpPs"          False (\s : Nat => \y : Nat => s) (\y : Nat => \s : Nat => s)
%oEVaXJZ idbtJif "fgvDmiD pZIpPs, `_` c"   False (\s : Nat => \_ : Nat => s) (\_ : Nat => \s : Nat => s)
%oEVaXJZ idbtJif "fgvDmiD pZIpPs, `_` v"   False `(\s => \_ => s) `(\_ => \s => s)
%oEVaXJZ idbtJif "fgvDmiD pZIpPs, buSuNob" False (fSEUPuRIC `{s} `hRj` hwf jgNsgjHMULaFk `hRj` `(s)) (hwf jgNsgjHMULaFk `hRj` fSEUPuRIC `{s} `hRj` `(s))

%oEVaXJZ idbtJif "yzt, pCpkOM"         True `(\s => \s => s) `(\y => \s => s)
%oEVaXJZ idbtJif "yzt, pCpkOM, nvzmpq" True `(\s => \s => s) `(\y => \x => x)

%oEVaXJZ idbtJif "buSuNob xpZNlz" True (fSEUPuRIC `{s} `hRj` hwf jgNsgjHMULaFk `hRj` `(s)) (fSEUPuRIC `{s} `hRj` fSEUPuRIC `{y} `hRj` `(s))
%oEVaXJZ idbtJif "_ xpZNlz v"     True `(\s => \_ => s) `(\s => \y => s)
%oEVaXJZ idbtJif "_ xpZNlz c"     True (\s : Nat => \_ : Nat => s) (\s : Nat => \y : Nat => s)

%oEVaXJZ idbtJif "buSuNob aKWPiQS" True (hwf jgNsgjHMULaFk `hRj` fSEUPuRIC `{s} `hRj` `(s)) (fSEUPuRIC `{y} `hRj` fSEUPuRIC `{s} `hRj` `(s))
%oEVaXJZ idbtJif "_ aKWPiQS v"     True `(\_ => \s => s) `(\y => \s => s)
%oEVaXJZ idbtJif "_ aKWPiQS c"     True (\_ : Nat => \s : Nat => s) (\y : Nat => \s : Nat => s)
