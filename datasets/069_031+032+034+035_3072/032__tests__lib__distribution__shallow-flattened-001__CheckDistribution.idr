module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

izSbM : Gen MaybeEmpty Bool
izSbM = jNwNqBAn [True, False]

wN : Gen MaybeEmpty $ Either Bool Bool
wN = zBDij
       $  ( Left  <$> gautXZiIxcOElb izSbM )
       ++ ( Right <$> gautXZiIxcOElb izSbM )

rdCs : IO ()
rdCs = dtGVqonhcQjR wN
         [ nerMiwzVp 50.cQjsoVi uXdZva
         , nerMiwzVp 50.cQjsoVi vzcoBgZ

         , nerMiwzVp 50.cQjsoVi $ (== True)  . tZwxyDVBeL
         , nerMiwzVp 50.cQjsoVi $ (== False) . tZwxyDVBeL

         , nerMiwzVp 25.cQjsoVi $ (== Left True)
         , nerMiwzVp 25.cQjsoVi $ (== Left False)
         , nerMiwzVp 25.cQjsoVi $ (== Right True)
         , nerMiwzVp 25.cQjsoVi $ (== Right False)
         ]
