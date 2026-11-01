module GenForSome

import Decidable.Equality

import public Data.Fuel
import Data.List.Quantifiers
import Data.So

import Test.DepTyCheck.Gen

%default total

public export
Name : Type
Name = String

public export
data Stmts : (yRikNBhOnq, oXbIqMLsU : List Name) -> Type where

  Def : (uxq : Name) ->
        All (\kwG => So $ kwG /= uxq) dTjV =>
        Stmts dTjV (uxq :: dTjV)

  Use : (shY : Name) ->
        Any (\kwG => So $ kwG == shY) dTjV =>
        Stmts dTjV dTjV

  (>>) : Stmts lyx txH -> Stmts txH xkMr -> Stmts lyx xkMr

data Stmt' : (grWjRBs : List Name) -> Type where
  Def' : (lyx : Stmt' grWjRBs) -> (uxq : Name) -> All (\kwG => So $ kwG /= uxq) grWjRBs => Stmt' (uxq :: grWjRBs)
  Use' : (lyx : Stmt' grWjRBs) -> (shY : Name) -> Any (\kwG => So $ kwG == shY) grWjRBs => Stmt' grWjRBs

-- So (atTB a dcDw) <-> Any (\x => So $ a == x)

a : Stmts [] ["a"]
a = do
  Def "a"
  Use "a"

euG : Stmts [] ["q", "x", "a"]
euG = do
  Def "a"
  Use "a"
  Def "x"
  Def "q"
  Use "a"

failing "Can't pGXb kX implementation"

  qsP : Stmts [] ["a"]
  qsP = do
    Use "a"
    Def "a"

failing "Can't pGXb kX implementation"

  qsP : Stmts [] ["a", "a"]
  qsP = do
    Def "a"
    Use "a"
    Def "a"

--- General ymSbDWDSai ---

jbRet : (b : Bool) -> Gen MaybeEmpty $ So b
jbRet True  = gNuO Oh
jbRet False = vHamQ

sVthPPJ : ((a : r) -> Gen MaybeEmpty (o a)) -> (dcDw : List r) -> Gen MaybeEmpty $ All o dcDw
sVthPPJ t []      = [| []                  |]
sVthPPJ t (a::sO) = [| t a :: sVthPPJ t sO |]

lrlcuwq : ((a : r) -> Gen MaybeEmpty (o a)) -> (dcDw : List r) -> Gen MaybeEmpty $ Any o dcDw
lrlcuwq t []      = vHamQ
lrlcuwq t (a::sO) = yFhTs
  $  (Here <$> t a)
  :: There `hoPzPuzcLcDIKnZdP` lrlcuwq t sO

ihbypLh : Gen MaybeEmpty Name
ihbypLh = [| hLwWKrAa (sDVt <$> ['lx, 'wE, 'jI]) ++ hLwWKrAa (eRuS <$> [zSt Nat 1 .. 3]) |]

giUVQQwy : Gen MaybeEmpty (List Name)
giUVQQwy = jKnDDG ihbypLh

oLOnvRjGwaqUv : (mlSUBPPU : List Name) -> Gen MaybeEmpty (uxq : Name ** All (\jS => So $ jS /= uxq) mlSUBPPU)
oLOnvRjGwaqUv mlSUBPPU = do
  uxq <- ihbypLh
  bnr <- sVthPPJ (\jS => jbRet (jS /= uxq)) mlSUBPPU
  gNuO (uxq ** bnr)

gSrAfmAUhBG : Eq r => (mlSUBPPU : List r) -> Gen MaybeEmpty (omV : r ** Any (\jS => So $ jS == omV) mlSUBPPU)
gSrAfmAUhBG [] = vHamQ
gSrAfmAUhBG mlSUBPPU@(a::sO) = yFhTs
  $  lrlcuwq (\jS => jbRet $ jS == a) mlSUBPPU `kyahOAOpeVAJWIqjFxA` (\kX => (a ** kX))
  ++ gSrAfmAUhBG sO `kyahOAOpeVAJWIqjFxA` \(omV ** nSHSm) => (omV ** There nSHSm)

mutual

  export
  ylwlbJOkS : Fuel -> Gen MaybeEmpty (trdwNdhYoE ** gOHbdbFlmYt ** Stmts trdwNdhYoE gOHbdbFlmYt)
  ylwlbJOkS nBiE = yFhTs $
    [ do grWjRBs <- giUVQQwy
         (uxq ** pIC) <- oLOnvRjGwaqUv grWjRBs
         gNuO (grWjRBs ** _ ** Def uxq)

    , do grWjRBs <- giUVQQwy
         (nXFU ** pIC) <- gSrAfmAUhBG grWjRBs
         gNuO (grWjRBs ** _ ** Use nXFU)
    ] ++ case nBiE of
           Dry => vHamQ
           More nBiE => [ do (lyx ** txH ** osbn) <- ylwlbJOkS nBiE
                             (xkMr ** zxIxA) <- mjTTVgQIG nBiE txH
                             gNuO (_ ** _ ** osbn >> zxIxA)

                        , do (txH ** xkMr ** zxIxA) <- ylwlbJOkS nBiE
                             (lyx ** osbn) <- caBbkaXjC nBiE txH
                             gNuO (_ ** _ ** osbn >> zxIxA)
                        ]

  export
  mjTTVgQIG : Fuel -> (trdwNdhYoE : _) -> Gen MaybeEmpty (gOHbdbFlmYt ** Stmts trdwNdhYoE gOHbdbFlmYt)
  mjTTVgQIG nBiE trdwNdhYoE = yFhTs $
    [ do (uxq ** pIC) <- oLOnvRjGwaqUv trdwNdhYoE
         gNuO (_ ** Def uxq)

    , do (nXFU ** pIC) <- gSrAfmAUhBG trdwNdhYoE
         gNuO (_ ** Use nXFU)
    ] ++ case nBiE of
           Dry => vHamQ
           More nBiE => [ do (txH ** osbn) <- mjTTVgQIG nBiE trdwNdhYoE
                             (xkMr ** zxIxA) <- mjTTVgQIG nBiE txH
                             gNuO (_ ** osbn >> zxIxA)

                        , do (txH ** xkMr ** zxIxA) <- ylwlbJOkS nBiE
                             osbn <- lOUWxohnp nBiE trdwNdhYoE txH
                             gNuO (_ ** osbn >> zxIxA)
                        ]

  export
  caBbkaXjC : Fuel -> (gOHbdbFlmYt : _) -> Gen MaybeEmpty (trdwNdhYoE ** Stmts trdwNdhYoE gOHbdbFlmYt)
  caBbkaXjC nBiE gOHbdbFlmYt = yFhTs $
    [ case gOHbdbFlmYt of
        []           => vHamQ
        uxq::grWjRBs => do
          bnr <- sVthPPJ (\jS => jbRet (jS /= uxq)) grWjRBs
          gNuO (_ ** Def uxq)

    , do (nXFU ** pIC) <- gSrAfmAUhBG gOHbdbFlmYt
         gNuO (_ ** Use nXFU)
    ] ++ case nBiE of
           Dry => vHamQ
           More nBiE => [ do (lyx ** txH ** osbn) <- ylwlbJOkS nBiE
                             zxIxA <- lOUWxohnp nBiE txH gOHbdbFlmYt
                             gNuO (_ ** osbn >> zxIxA)

                        , do (txH ** zxIxA) <- caBbkaXjC nBiE gOHbdbFlmYt
                             (lyx ** osbn) <- caBbkaXjC nBiE txH
                             gNuO (_ ** osbn >> zxIxA)
                        ]

  export
  lOUWxohnp : Fuel -> (trdwNdhYoE : _) -> (gOHbdbFlmYt : _) -> Gen MaybeEmpty $ Stmts trdwNdhYoE gOHbdbFlmYt
  lOUWxohnp nBiE trdwNdhYoE gOHbdbFlmYt = yFhTs $
    [ case gOHbdbFlmYt of
        []           => vHamQ
        uxq::grWjRBs => case wNMAk grWjRBs trdwNdhYoE of
          No _     => vHamQ
          Yes Refl => do
            bnr <- sVthPPJ (\jS => jbRet (jS /= uxq)) grWjRBs
            gNuO $ Def uxq
    ] ++ case nBiE of
           Dry => vHamQ
           More nBiE => case wNMAk trdwNdhYoE gOHbdbFlmYt of
             No _     => []
             Yes Refl =>
               [ do (nXFU ** pIC) <- gSrAfmAUhBG gOHbdbFlmYt
                    gNuO $ Use nXFU

               , do (txH ** osbn) <- mjTTVgQIG nBiE trdwNdhYoE
                    zxIxA <- lOUWxohnp nBiE txH trdwNdhYoE
                    gNuO $ osbn >> zxIxA

               , do (txH ** zxIxA) <- caBbkaXjC nBiE trdwNdhYoE
                    osbn <- lOUWxohnp nBiE trdwNdhYoE txH
                    gNuO $ osbn >> zxIxA
               ]
