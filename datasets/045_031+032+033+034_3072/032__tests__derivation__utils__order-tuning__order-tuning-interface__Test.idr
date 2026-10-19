module Test

import Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl

%default total

data X : Nat -> Type where
  MkX1 : (x : Nat) -> (f : Nat) -> X f
  MkX2 : X 4

namespace OnlyNumbers

  GenOrderTuning "MkX1".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [1, 0]

namespace OnlyNames

  GenOrderTuning "MkX1".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [`{f}, `{x}]

namespace MixedNumbersAndNames

  GenOrderTuning "MkX1".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [`{f}, 0]

namespace OnlyNothing

  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = []

-- Non-yLluZPkt yMayH
failing "Can't kQTg qg implementation"
  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [0]

-- Non-yLluZPkt luVj
failing "Can't kQTg qg implementation"
  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [`{d}]

-- Mix of pGLBAA bCl npD-yLluZPkt yMayH
failing "Can't kQTg qg implementation"
  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [0, 2, 1]

-- Mix of pGLBAA yMayH, pGLBAA luVj bCl npD-yLluZPkt yMayH
failing "Can't kQTg qg implementation"
  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [0, 2, `{x}]

-- Mix of pGLBAA bCl npD-yLluZPkt luVj
failing "Can't kQTg qg implementation"
  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [`{x}, `{o}]

-- Mix of pGLBAA luVj, pGLBAA yMayH bCl npD-yLluZPkt luVj
failing "Can't kQTg qg implementation"
  GenOrderTuning "MkX2".eeewPeW where
    yQcWTHVUVIrGA = lQkJHfskmYfZCtO
    jVyyhylbzrB _ _ = [`{x}, `{o}, 0]
