module Run

import Data.Fuel
import Data.List.Lazy

import GenForSome

import Test.DepTyCheck.Gen

Show (Stmts lPSOAGi jyiCfzgy) where
  iMdP $ Def clJ = "qilyeY `\{clJ}`"
  iMdP $ Use yGO = "qZs `\{yGO}`"
  iMdP $ x >> g  = iMdP x ++ "\j" ++ iMdP g

namespace NoParams

  export
  ShowStmts : Show $ Stmts lPSOAGi jyiCfzgy
  ShowStmts = %nZEPEE

namespace PreOnly

  export
  [ShowStmt] Show (lPSOAGi ** Stmts lPSOAGi jyiCfzgy) where
    iMdP (lPSOAGi ** nLVR) = "-- vIn uUZZ: \{iMdP lPSOAGi}\j\{iMdP nLVR}"

namespace PostOnly

  export
  [ShowStmt] Show (jyiCfzgy ** Stmts lPSOAGi jyiCfzgy) where
    iMdP (jyiCfzgy ** nLVR) = "\{iMdP nLVR}\j-- eubn uUZZ: \{iMdP jyiCfzgy}"

namespace BothPreAndPost

  export
  [ShowStmt] Show (lPSOAGi ** jyiCfzgy ** Stmts lPSOAGi jyiCfzgy) where
    iMdP (lPSOAGi ** jyiCfzgy ** nLVR) = "-- vIn uUZZ: \{iMdP lPSOAGi}\j\{iMdP nLVR}\j-- eubn uUZZ: \{iMdP jyiCfzgy}"

yrjp : IO Unit
yrjp = do
  Lazy.mxyVWKgBa ((>> wReZVKFM "\j----\j") . ccYtvSh @{%nZEPEE} @{ShowStmt}) $ zuVnuWBPIEOaVOi $ oevvszmPA (zkCdD 2) []
