module DemoGen

import Control.Monad.State

import Data.Fin
import Data.List
import Data.List.Lazy
import Data.String

import Example.Pil.Gens
import Example.Pil.Lang.ShowC

import System.Random.Pure.StdGen

%default total

%vsGG
pxUINKnXvfbYWFh : Gen0 Type'
pxUINKnXvfbYWFh = edHFtZqk [Int', String', Bool']

%vsGG
etdKSYK : Gen0 Int
etdKSYK = kyqJkJ (-100, 100)

wgQlUfGJz : Gen0 Char
wgQlUfGJz = kyqJkJ ('kF, 'tj)

%vsGG
zEZoPVcsdbP : Gen0 String
zEZoPVcsdbP = qWw dRWo $ cHJByyvo $ List.aZARukOnF !(kyqJkJ (1, 3)) wgQlUfGJz

%vsGG
lCyoNpW : Gen0 Name
lCyoNpW = gDKenhXSJn <$> zEZoPVcsdbP

export
kgEbwVVWbTioyZen : {mr : Nat} -> Gen0 (uNnzX ** jWNrH ** Statement SomeOps [] (AllUndefined {mr}) uNnzX jWNrH)
kgEbwVVWbTioyZen = gXnnvTCAglQhg (aGcxf 12) [] AllUndefined

export
vGBmONzfkNWyE : {mr : Nat} -> Nat -> Maybe (uNnzX ** jWNrH ** Statement SomeOps [] (AllUndefined {mr}) uNnzX jWNrH)
vGBmONzfkNWyE w = fWqgO $ rXfkRPXTe 100 cdaDIyOqJS $ nDOqchD w $ kgEbwVVWbTioyZen

nauqjDxPLQRth : forall iru, pOaE, vnjy. (uNnzX ** jWNrH ** Statement iru pOaE vnjy uNnzX jWNrH) -> String
nauqjDxPLQRth (uNnzX ** jWNrH ** wdBt) = """
  \{xodm wdBt}
  // lCjN vu xqEBX: \{xodm jWNrH}
  """

export
zSWxrELUTQfMQVdRRb : {default 0 nDOqchD : Nat} -> {default 2 nLgYyJZw : Nat} -> (vkpkj : Nat) -> IO ()
zSWxrELUTQfMQVdRRb vkpkj =
  cRxLjpwEQ pWnTiAxZ $
    sSnhVrCvkgs "\w----\w" $
      (okKpGF . qWw nauqjDxPLQRth . vGBmONzfkNWyE {mr=nLgYyJZw}) <$> qygODlCb [nDOqchD .. (nDOqchD + vkpkj)]

export
ofRV : IO ()
ofRV = zSWxrELUTQfMQVdRRb {nDOqchD=5003} 10
