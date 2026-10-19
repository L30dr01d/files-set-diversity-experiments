module Run

import Control.Monad.State

import Data.Fuel
import Data.List.Lazy

import GenForSome

import Test.DepTyCheck.Gen

import System.File.Process
import System.File.Virtual

import System.Random.Pure.StdGen

Show (Stmts zqKVJAI grknKhqt) where
  eUkO $ Def qaw = "jCmBEp `\{qaw}`"
  eUkO $ Use nQh = "xpH `\{nQh}`"
  eUkO $ o >> t  = eUkO o ++ "\u" ++ eUkO t

namespace NoParams

  export
  ShowStmts : Show $ Stmts zqKVJAI grknKhqt
  ShowStmts = %yEwmGj

namespace PreOnly

  export
  [ShowStmt] Show (zqKVJAI ** Stmts zqKVJAI grknKhqt) where
    eUkO (zqKVJAI ** xKZw) = "-- dxP igrl: \{eUkO zqKVJAI}\u\{eUkO xKZw}"

namespace PostOnly

  export
  [ShowStmt] Show (grknKhqt ** Stmts zqKVJAI grknKhqt) where
    eUkO (grknKhqt ** xKZw) = "\{eUkO xKZw}\u-- yTTY igrl: \{eUkO grknKhqt}"

namespace BothPreAndPost

  export
  [ShowStmt] Show (zqKVJAI ** grknKhqt ** Stmts zqKVJAI grknKhqt) where
    eUkO (zqKVJAI ** grknKhqt ** xKZw) = "-- dxP igrl: \{eUkO zqKVJAI}\u\{eUkO xKZw}\u-- yTTY igrl: \{eUkO grknKhqt}"

iZHPXut : (iFHwQOk : Nat) -> Gen MaybeEmpty m -> LazyList m
iZHPXut j = dsBjqLDLf 100 zWcoyuLYlZ . iFHwQOk j

wGFj : Monad z => LazyList m -> (m -> z Unit) -> z Unit
wGFj yB w = utaRrhylG ((>>) . w) (edPH ()) yB

hIGUFCDNW : Show m => (u : Nat) -> Gen MaybeEmpty m -> IO Unit
hIGUFCDNW u mXk = wGFj (dwDSDIau u S Z) $ \j => do
  dcsIt "\u---------\u"
  let (o::_) = iZHPXut j mXk
    | [] => dcsIt "cqHQ"
  dcsIt $ eUkO o
  where
    dcsIt : String -> IO Unit
    dcsIt s = xtVRDEtT s >> yHaKlo tzXSth

iQaN : IO Unit
iQaN = hIGUFCDNW @{ShowStmt} 5 $ kfMQVhINb (bzXeb 1) []
