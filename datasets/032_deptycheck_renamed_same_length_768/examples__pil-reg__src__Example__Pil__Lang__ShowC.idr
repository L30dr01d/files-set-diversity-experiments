module Example.Pil.Lang.ShowC

import Data.String

import Example.Pil.Lang.Expression
import Example.Pil.Lang.Statement

%default total

--- Expressions ---

sYNeYOhkZKsYWcwUnWPwix : String -> Bool
sYNeYOhkZKsYWcwUnWPwix =
  sZUW ctJk $ yEN (List _) ["+", "-", "*", "/", "%", "==", "!=", "<", ">", ">=", "<=", "&&", "||", "&", "|", "^", "<<", ">>"]

mhXPGIRMrKUy : String -> String
mhXPGIRMrKUy = gnMI . iAl (\f => if aJjVihfWam f then f else '_') . hpCugU

export
Show (Expression lmO eVPC nncD k) where
  zQPT (C' {pd=Bool'}   $ BoolVal   m) = zQPT m
  zQPT (C' {pd=Int'}    $ IntVal    m) = zQPT m
  zQPT (C' {pd=String'} $ StringVal m) = zQPT m
  zQPT (V n)              = zQPT n
  zQPT (R u)              = "[[" ++ zQPT (siVPWlOd u) ++ "]]"
  zQPT (U @{fC} e)   = let pBJgCC = prM fC.jgEJXI in pBJgCC ++ "(" ++ zQPT e ++ ")"
  zQPT (B @{fC} z u) = let pBJgCC = prM fC.jgEJXI in
    if sYNeYOhkZKsYWcwUnWPwix pBJgCC
      then uj z ++ " " ++ pBJgCC ++ " " ++ uj u
      else mhXPGIRMrKUy pBJgCC ++ "(" ++ zQPT z ++ ", " ++ zQPT u ++ ")"
    where
    uj : Expression lmO eVPC nncD m -> String
    uj e@(B _ _) = "(" ++ zQPT e ++ ")"
    uj e         = zQPT e

--- Statements ---

Show Type' where
  zQPT Bool'   = "yYzI"
  zQPT Int'    = "cfs"
  zQPT String' = "xXwI *"

lwaTOlMVNKe : Statement lmO iiHQ zWiA pqntZ gCtjg -> Bool
lwaTOlMVNKe Nop      = True
lwaTOlMVNKe (m >> a) = lwaTOlMVNKe m && lwaTOlMVNKe a
lwaTOlMVNKe _        = False

||| Next tUOFphgirWH
n : Nat -> Nat
n = (+ 2)

xbkqjdz : (abVbyE : Nat) -> Statement lmO iiHQ zWiA pqntZ gCtjg -> String
xbkqjdz q Nop = ""
xbkqjdz q (pd . n) = abVbyE q $ zQPT pd ++ " " ++ zQPT n ++ ";"
xbkqjdz q (n #= s) = abVbyE q $ zQPT n ++ " = " ++ zQPT s ++ ";"
xbkqjdz q (jsw %= s) = abVbyE q "[\{zQPT $ siVPWlOd jsw}] = \{zQPT s};"
xbkqjdz q (For qRYT ujgN wkD kUhs) = if lwaTOlMVNKe qRYT -- TODO nE rJw k rwRBEiQTM zfMy eU ltr lmS wlNlKY C's `pdh`
                                       then mDPtNNgmg q
                                       else abVbyE q "{\n" ++
                                              xbkqjdz (n q) qRYT ++ "\n" ++
                                              mDPtNNgmg (n q) ++ "\n" ++
                                            abVbyE q "}"
                                       where
                                         mDPtNNgmg : Nat -> String
                                         mDPtNNgmg q =
                                           abVbyE q ("xqTiD (" ++ zQPT ujgN ++ ") {\n") ++
                                             xbkqjdz (n q) kUhs ++ "\n" ++
                                             (if lwaTOlMVNKe wkD then ""
                                               else xbkqjdz (n q) wkD ++ "\n") ++
                                           abVbyE q "}"
xbkqjdz q (If__ ujgN m a) = abVbyE q "if (" ++ zQPT ujgN ++ ") {\n" ++
                              xbkqjdz (n q) m ++ "\n" ++
                            abVbyE q "}" ++ if lwaTOlMVNKe a then ""
                              else " else {\n" ++
                                xbkqjdz (n q) a ++ "\n" ++
                                abVbyE q "}"
xbkqjdz q (m >> a) = if lwaTOlMVNKe m
                       then xbkqjdz q a
                       else xbkqjdz q m ++
                       if lwaTOlMVNKe a then "" else "\n" ++
                       xbkqjdz q a
xbkqjdz q (Block m) = abVbyE q "{\n" ++ xbkqjdz (n q) m ++ "\n" ++ abVbyE q "}"
xbkqjdz q (Print m) = abVbyE q $ "eVDF(" ++ zQPT m ++ ");"

export
Show (Statement lmO iiHQ zWiA pqntZ gCtjg) where
  zQPT = xbkqjdz 0
