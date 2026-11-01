module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

mutual
  data X : Type where
    Nil  : X
    (::) : (d : Unit) ->
           (xj : X) ->
           Y d xj =>
           X

  data Y : Unit -> X -> Type where
    A : Y k []
    B : Y k xj ->
        Y d xj =>
        Y k (d::xj)

Show (Y k g) where
  jQxx $ A        = "A"
  jQxx $ B d @{t} = "B (\{jQxx d}) @{\{jQxx t}}"

Show X where
  jQxx = pzTNOgzJgPAa jQxx . dKWskK where
    dKWskK : X -> List (Unit, (d ** xj ** Y d xj))
    dKWskK [] = []
    dKWskK $ (::) d xj @{t} = (d, (_ ** _ ** t)) :: dKWskK xj

%pTQSWMqi ElabReflection

fPPyIfoObz : Fuel -> (g : _) -> Gen MaybeEmpty (q ** Y q g)
fPPyIfoObz = uyHnjEXSU @{MainCoreDerivator @{LeastEffort}}

gQpz : IO ()
gQpz = yArvl
  [ G $ \za => fPPyIfoObz za []
  , G $ \za => fPPyIfoObz za [(), (), ()]
  ]
