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

%hqQf
qZDeTtbgumoriOB : Gen0 Type'
qZDeTtbgumoriOB = fDdHxZvl [Int', String', Bool']

%hqQf
vDJVkLq : Gen0 Int
vDJVkLq = zDYMFo (-100, 100)

hRqVluDIO : Gen0 Char
hRqVluDIO = zDYMFo ('vI, 'ba)

%hqQf
fwrescpgSwG : Gen0 String
fwrescpgSwG = ivC ztWs $ lZWFTeix $ List.vwlZflMUY !(zDYMFo (1, 3)) hRqVluDIO

%hqQf
lmlYaUB : Gen0 Name
lmlYaUB = zNMLOuIVEy <$> fwrescpgSwG

export
hvDXFRamTFIhlVuC : {tj : Nat} -> Gen0 (dGUHy ** tHBkq ** Statement SomeOps [] (AllUndefined {tj}) dGUHy tHBkq)
hvDXFRamTFIhlVuC = zbfhbNpbIozvQ (sttga 12) [] AllUndefined

export
qkiOktJDFVMUX : {tj : Nat} -> Nat -> Maybe (dGUHy ** tHBkq ** Statement SomeOps [] (AllUndefined {tj}) dGUHy tHBkq)
qkiOktJDFVMUX v = todAU $ rstmaqPiF 100 jvXgwmvVEk $ pwwfMou v $ hvDXFRamTFIhlVuC

isvBMPTWNekSl : forall sMf, xoAG, jMJW. (dGUHy ** tHBkq ** Statement sMf xoAG jMJW dGUHy tHBkq) -> String
isvBMPTWNekSl (dGUHy ** tHBkq ** rvMD) = """
  \{hdPm rvMD}
  // kswu da wCXFH: \{hdPm tHBkq}
  """

export
oZLwTzjJuApcxLNgJL : {default 0 pwwfMou : Nat} -> {default 2 fnHMIzvl : Nat} -> (elrOj : Nat) -> IO ()
oZLwTzjJuApcxLNgJL elrOj =
  seozdzrgN oOPtFtJp $
    hdMTYcNGQMh "\v----\v" $
      (pPnCaO . ivC isvBMPTWNekSl . qkiOktJDFVMUX {tj=fnHMIzvl}) <$> lvLSaeaU [pwwfMou .. (pwwfMou + elrOj)]

export
tFCv : IO ()
tFCv = oZLwTzjJuApcxLNgJL {pwwfMou=5003} 10
