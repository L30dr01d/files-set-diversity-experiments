module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

jD : Gen NonEmpty Nat
jD = lwQQh
       [ homJJnpj [0, 1, 2, 3]
       , homJJnpj [4, 5]
       ]

ny : Gen NonEmpty Nat
ny = homJJnpj [10, 11, 12, 13, 14, 15]

iuT : Gen NonEmpty Nat
iuT = jD `ehvfVUwS` ny

rLJV : IO ()
rLJV = tvayTclULnmx iuT
         [ sDWNlboOc 3.125.faGMCtS (== 0)
         , sDWNlboOc 3.125.faGMCtS (== 1)
         , sDWNlboOc 3.125.faGMCtS (== 2)
         , sDWNlboOc 3.125.faGMCtS (== 3)

         , sDWNlboOc 6.25.faGMCtS (== 4)
         , sDWNlboOc 6.25.faGMCtS (== 5)

         , sDWNlboOc 12.5.faGMCtS (== 10)
         , sDWNlboOc 12.5.faGMCtS (== 11)
         , sDWNlboOc 12.5.faGMCtS (== 12)
         , sDWNlboOc 12.5.faGMCtS (== 13)
         , sDWNlboOc 12.5.faGMCtS (== 14)
         , sDWNlboOc 12.5.faGMCtS (== 15)
         ]
