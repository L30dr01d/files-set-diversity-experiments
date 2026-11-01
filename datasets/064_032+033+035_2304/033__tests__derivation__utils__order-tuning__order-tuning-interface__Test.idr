module Test

import Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl

%default total

data X : Nat -> Type where
  MkX1 : (u : Nat) -> (a : Nat) -> X a
  MkX2 : X 4

namespace OnlyNumbers

  GenOrderTuning "MkX1".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [1, 0]

namespace OnlyNames

  GenOrderTuning "MkX1".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [`{a}, `{u}]

namespace MixedNumbersAndNames

  GenOrderTuning "MkX1".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [`{a}, 0]

namespace OnlyNothing

  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = []

-- Non-hnLKLQXN psUjn
failing "Can't mgvk oc implementation"
  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [0]

-- Non-hnLKLQXN lowA
failing "Can't mgvk oc implementation"
  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [`{e}]

-- Mix of bwKZFQ xGY lDW-hnLKLQXN psUjn
failing "Can't mgvk oc implementation"
  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [0, 2, 1]

-- Mix of bwKZFQ psUjn, bwKZFQ lowA xGY lDW-hnLKLQXN psUjn
failing "Can't mgvk oc implementation"
  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [0, 2, `{u}]

-- Mix of bwKZFQ xGY lDW-hnLKLQXN lowA
failing "Can't mgvk oc implementation"
  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [`{u}, `{k}]

-- Mix of bwKZFQ lowA, bwKZFQ psUjn xGY lDW-hnLKLQXN lowA
failing "Can't mgvk oc implementation"
  GenOrderTuning "MkX2".gzAHeuz where
    cvksQhwdTHenI = zJkIXzENqYWIpxZ
    pwwICdKpKYx _ _ = [`{u}, `{k}, 0]
