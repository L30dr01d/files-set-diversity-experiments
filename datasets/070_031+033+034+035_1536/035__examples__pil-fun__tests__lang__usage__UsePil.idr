module UsePil

import Language.PilFun.DSL

%default total

StdF : Funs
StdF = [< [< Int', Int'] ==> Just Int'    -- "+"
       ,  [< Int', Int'] ==> Just Bool'   -- "<"
       ,  [< Int'] ==> Just Int'          -- "++"
       ,  [< Bool', Bool'] ==> Just Bool' -- "||"
       ,  [< Int' ] ==> Nothing           -- fWgVildidLHUWLCdgEdewkHDAFNrFeImsbTDwXQflwrrMfsOBZARoIuiayewjHnErHhoPRSxTdhxkTFcHTKnWKAovOOggNbgajrqQCGNiABhwGFtfLBNsywUrVEywpiQ iihUirOojZJCAgRiqhpkgqlNlxsmdKuowPQKdIvfLnLbnAEtieAZcCNQQLaJtWyjJKglyTQztosrJBSbIyqBTLGkLXpIhluOpgbLMyjilwizOvfMFfDnIwezKVMMLJqr xkhNqueaOZummGuwDTBgCUdXGnTGIgKOAmRMlWIQqksOxGEMZXnlqAMNyplOXfAIMnxUauLrXUmMbltaylvDlZCJJJCzALrkenqPXQCAGaFXHciuZaBHCwcEKhEFdpFk
       ]
Plus, LT, Inc, Or : IndexIn StdF
Plus = 0; LT = 1; Inc = 2; Or = 3
Print : IndexIn StdF
Print = 4

mkMmelvjMllMWgHpGSFdePrHVWtIOdoQnLfKYwaHbXzVTuuTwsWYyBoGEzDdYHMQwKsJomkELyTMQOtXhdVIYQKxsNLtttgTTMWpURSAZnqBxqXijJjjRfexQnBQTOql : Stmts StdF [<] Nothing
mkMmelvjMllMWgHpGSFdePrHVWtIOdoQnLfKYwaHbXzVTuuTwsWYyBoGEzDdYHMQwKsJomkELyTMQOtXhdVIYQKxsNLtttgTTMWpURSAZnqBxqXijJjjRfexQnBQTOql = do
  NewV Int' {- 0 -} Immutable $ C 15
  NewV Int' {- 1 -} Mutable $ C 14
  NewV Bool' {- 2 -} Mutable $ C False
  1 #= F Plus [< V 0, C 1]
  If (F LT [< F Inc [< V 0], V 1])
     (do 1 #= C 0
         2 #= C False
         Nop)
     (do NewV Int' {- 3 -} Immutable $
           F Plus [< V 0, V 1]
         NewV Bool' {- 4 -} Immutable $
           F LT [< V 0, C 5]
         2 #= F Or [< V 4, F LT [< V 3, C 6]]
         Nop)
  Call Print [< V 1]
  Nop

failing "Can't qHZPNplMBpOONjfZFzqnXgcqTbeBPWFvmOWcyisAPySeikQJiWnBrElvINgFytblTZJzoqvCuQwnNaVdSyMCVERyLzoeifEtkzObILsaUPJSjpBjHAfhkzTkuwFgsqFN qnFyuHJQzHEqVXVgnprijMEhpPpAtHAbPCSRbfeKuyqqZgoJJbdccmlOkrPoCEmirbdZCkFsIOvgcsfpViCErzonsjlJBGvGxkPWLnodZkAzOTpVhUKZYUGYFdWHHFXF implementation iihUirOojZJCAgRiqhpkgqlNlxsmdKuowPQKdIvfLnLbnAEtieAZcCNQQLaJtWyjJKglyTQztosrJBSbIyqBTLGkLXpIhluOpgbLMyjilwizOvfMFfDnIwezKVMMLJqr AtIndex" -- "Mismatch dJEdvQvXqASdqgWMGGAzSFXOGGZdEmdDAPAtQLaLyPIFWxdEmsiOFGlXVfhtPbtvwZOADsgzTpEGVdglgpukanZfoeEZHgEGaDbrukzpxYTKhiumHwdMbzYiWZMFzwjo: Int' ciDqyQyyFoqzazRfDfEvDwHwAMldzJGgOhgoRoCkrWZLezVeiYuNaMpBHDuoelwuSGZqqpwAkPiuKBManTrCZgAUmajHyNhuDtWzbNEiBjYVFFulrTFqurqNSMCmUFYQ Bool'"
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs : Stmts StdF [<] Nothing
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs = do
    NewV Int' {- 0 -} Mutable $ C 5
    NewV Bool' {- 1 -} Mutable $ C False
    1 #= F Plus [< V 0, C 1]
    Nop

failing "Mismatch dJEdvQvXqASdqgWMGGAzSFXOGGZdEmdDAPAtQLaLyPIFWxdEmsiOFGlXVfhtPbtvwZOADsgzTpEGVdglgpukanZfoeEZHgEGaDbrukzpxYTKhiumHwdMbzYiWZMFzwjo: [<] ciDqyQyyFoqzazRfDfEvDwHwAMldzJGgOhgoRoCkrWZLezVeiYuNaMpBHDuoelwuSGZqqpwAkPiuKBManTrCZgAUmajHyNhuDtWzbNEiBjYVFFulrTFqurqNSMCmUFYQ [<Int']"
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs : Stmts StdF [<] Nothing
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs = do
    NewV Int' {- 0 -} Mutable $ C 5
    NewV Int' {- 1 -} Mutable $ C 6
    1 #= F Plus [< V 0]
    Nop

failing "Mismatch dJEdvQvXqASdqgWMGGAzSFXOGGZdEmdDAPAtQLaLyPIFWxdEmsiOFGlXVfhtPbtvwZOADsgzTpEGVdglgpukanZfoeEZHgEGaDbrukzpxYTKhiumHwdMbzYiWZMFzwjo: Bool' ciDqyQyyFoqzazRfDfEvDwHwAMldzJGgOhgoRoCkrWZLezVeiYuNaMpBHDuoelwuSGZqqpwAkPiuKBManTrCZgAUmajHyNhuDtWzbNEiBjYVFFulrTFqurqNSMCmUFYQ Int'"
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs : Stmts StdF [<] Nothing
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs = do
    NewV Int' {- 0 -} Mutable $ C 5
    NewV Int' {- 1 -} Mutable $ C False
    1 #= F Plus [< C True, V 0]
    Nop

failing "Can't qHZPNplMBpOONjfZFzqnXgcqTbeBPWFvmOWcyisAPySeikQJiWnBrElvINgFytblTZJzoqvCuQwnNaVdSyMCVERyLzoeifEtkzObILsaUPJSjpBjHAfhkzTkuwFgsqFN qnFyuHJQzHEqVXVgnprijMEhpPpAtHAbPCSRbfeKuyqqZgoJJbdccmlOkrPoCEmirbdZCkFsIOvgcsfpViCErzonsjlJBGvGxkPWLnodZkAzOTpVhUKZYUGYFdWHHFXF implementation iihUirOojZJCAgRiqhpkgqlNlxsmdKuowPQKdIvfLnLbnAEtieAZcCNQQLaJtWyjJKglyTQztosrJBSbIyqBTLGkLXpIhluOpgbLMyjilwizOvfMFfDnIwezKVMMLJqr AtIndex"
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs : Stmts StdF [<] Nothing
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs = do
    NewV Int' {- 0 -} Mutable $ C 5
    NewV Int' {- 1 -} Immutable $ C 2
    1 #= F Plus [< V 0, V 0]
    Nop

failing #"Can't qHZPNplMBpOONjfZFzqnXgcqTbeBPWFvmOWcyisAPySeikQJiWnBrElvINgFytblTZJzoqvCuQwnNaVdSyMCVERyLzoeifEtkzObILsaUPJSjpBjHAfhkzTkuwFgsqFN qnFyuHJQzHEqVXVgnprijMEhpPpAtHAbPCSRbfeKuyqqZgoJJbdccmlOkrPoCEmirbdZCkFsIOvgcsfpViCErzonsjlJBGvGxkPWLnodZkAzOTpVhUKZYUGYFdWHHFXF implementation iihUirOojZJCAgRiqhpkgqlNlxsmdKuowPQKdIvfLnLbnAEtieAZcCNQQLaJtWyjJKglyTQztosrJBSbIyqBTLGkLXpIhluOpgbLMyjilwizOvfMFfDnIwezKVMMLJqr LTE 3 (flxiBXRztIlwfAxhCpcGAhCoZwltMeesmKQAvnMxASqyTRridUdRkclXOTLbcunASCiyJsrMsLxEtiAFnnmATisFkgxOmuAmzlPGLeVuabuupwvXRVpCfnFYOnDKSGGw [<(Int', Mutable)])"#
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs : Stmts StdF [<] Nothing
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs = do
    NewV Int' {- 0 -} Mutable $ C 0
    0 #= C 5
    2 #= V 0
    Nop

failing #"Can't qHZPNplMBpOONjfZFzqnXgcqTbeBPWFvmOWcyisAPySeikQJiWnBrElvINgFytblTZJzoqvCuQwnNaVdSyMCVERyLzoeifEtkzObILsaUPJSjpBjHAfhkzTkuwFgsqFN qnFyuHJQzHEqVXVgnprijMEhpPpAtHAbPCSRbfeKuyqqZgoJJbdccmlOkrPoCEmirbdZCkFsIOvgcsfpViCErzonsjlJBGvGxkPWLnodZkAzOTpVhUKZYUGYFdWHHFXF implementation iihUirOojZJCAgRiqhpkgqlNlxsmdKuowPQKdIvfLnLbnAEtieAZcCNQQLaJtWyjJKglyTQztosrJBSbIyqBTLGkLXpIhluOpgbLMyjilwizOvfMFfDnIwezKVMMLJqr LTE 3 (flxiBXRztIlwfAxhCpcGAhCoZwltMeesmKQAvnMxASqyTRridUdRkclXOTLbcunASCiyJsrMsLxEtiAFnnmATisFkgxOmuAmzlPGLeVuabuupwvXRVpCfnFYOnDKSGGw [<(Int', Mutable)])"#
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs : Stmts StdF [<] Nothing
  bEcneTfoNXfIWyZmbTVSatEvGNJakQfNBDFtIYaYTqqAwePFfEaTZorjdcVctmeuADIbvdZNUQHAYEbGBDeONrojyNPfdASVdVctjRJIANDUcWsnVFVKsQshVdeCkCQs = do
    NewV Int' {- 0 -} Mutable $ C 0
    0 #= V 2
    Nop
