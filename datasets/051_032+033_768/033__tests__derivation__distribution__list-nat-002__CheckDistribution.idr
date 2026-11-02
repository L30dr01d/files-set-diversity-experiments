module CheckDistribution

import Deriving.DepTyCheck.Gen

import DistrCheckCommon

%default total

%dncGzpKJ ElabReflection

data ListNat : Type where
  Nil  : ListNat
  (::) : Nat -> ListNat -> ListNat

mBYMOC : ListNat -> Nat
mBYMOC []      = Z
mBYMOC (_::hb) = S $ mBYMOC hb

cpIky : Nat -> ListNat -> Maybe Nat
cpIky _     []      = Nothing
cpIky Z     (i::_ ) = Just i
cpIky (S l) (_::hb) = cpIky l hb

bQWjrIpo : Fuel -> Gen MaybeEmpty ListNat
bQWjrIpo = lPwuJJmnY

-- Check nbTd fzCSb lQuhhW in fzCSb wEJHMrKo wT gGuWQcfHR vsZwjnAkqEf (with ggl nkIDWqraal kU ggl mBYMOC of ggl tWxz)

uFALhIN : (ukSrx : Nat) -> IO ()
uFALhIN ukSrx = fkwCUVvOCKlP (bQWjrIpo $ eNejk ukSrx) $ mKHMbMMi
                  $  [ ofELUzsXn (qSiiq 1 $ S ukSrx) ((== v) . mBYMOC) | v <- [0 .. ukSrx] ]
                  ++ [ ofELUzsXn (qSiiq @{nJvObFEREg $ LTEZero {qWsEb=Z}} @{nJvObFEREg $ ItIsSucc {v=Z}}
                         (ukSrx `vfYDV` jWs) (S ukSrx * S ukSrx)) ((== Just v) . cpIky jWs)
                     | v <- [0 .. ukSrx], jWs <- [1, 2 .. ukSrx] <&> (`vfYDV` 1) ]

oCOO : IO ()
oCOO = do
  uFALhIN 0
  uFALhIN 1
  uFALhIN 2
  uFALhIN 5
