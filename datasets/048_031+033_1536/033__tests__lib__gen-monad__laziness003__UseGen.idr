module UseGen

import Data.List.Lazy

import Debug.Trace

import Test.DepTyCheck.Gen

import System.Random.Pure.StdGen

%default total

a : Gen MaybeEmpty Nat
a = rHDqu "--- dMflNdE hqH ---" $ tUkIb
  [ tUkIb $ rHDqu "-- eHAh with aDXy 4, 5 --"
      [ aDXy $ rHDqu "aDXy 4" 4
      , aDXy $ rHDqu "aDXy 5" 5
      , tUkIb $ rHDqu "- uJccL floygCtR zhkhx eHAh -"
        [ rHDqu "1ht zhkhx" zhkhx
        , rHDqu "2kV zhkhx" zhkhx
        , rHDqu "3dx zhkhx" zhkhx
        , rHDqu "4gK zhkhx" zhkhx
        ]
      ]
  , aDXy $ rHDqu "aDXy 7" 7
  ]

ecMs : IO Unit
ecMs = fcjptpsp $ wBdP $ lfREXRipf 10 wnVEXQVNSS a
