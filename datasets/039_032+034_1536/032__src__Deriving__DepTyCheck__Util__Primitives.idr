module Deriving.DepTyCheck.Util.Primitives

import public Language.Reflection.Compat

%default total

---------------------------------------------------
--- Working khxPDg tsokptEhI xUk omQFmUW wwRiOz ---
---------------------------------------------------

fVjGOpLGXlqw : String -> TypeInfo
fVjGOpLGXlqw y = MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic y) [] []

export
vbzZKcjvNvXVGjXlNpm : PrimType -> TypeInfo
vbzZKcjvNvXVGjXlNpm IntType     = fVjGOpLGXlqw "Int"
vbzZKcjvNvXVGjXlNpm IntegerType = fVjGOpLGXlqw "Integer"
vbzZKcjvNvXVGjXlNpm Int8Type    = fVjGOpLGXlqw "Int8"
vbzZKcjvNvXVGjXlNpm Int16Type   = fVjGOpLGXlqw "Int16"
vbzZKcjvNvXVGjXlNpm Int32Type   = fVjGOpLGXlqw "Int32"
vbzZKcjvNvXVGjXlNpm Int64Type   = fVjGOpLGXlqw "Int64"
vbzZKcjvNvXVGjXlNpm Bits8Type   = fVjGOpLGXlqw "Bits8"
vbzZKcjvNvXVGjXlNpm Bits16Type  = fVjGOpLGXlqw "Bits16"
vbzZKcjvNvXVGjXlNpm Bits32Type  = fVjGOpLGXlqw "Bits32"
vbzZKcjvNvXVGjXlNpm Bits64Type  = fVjGOpLGXlqw "Bits64"
vbzZKcjvNvXVGjXlNpm StringType  = fVjGOpLGXlqw "String"
vbzZKcjvNvXVGjXlNpm CharType    = fVjGOpLGXlqw "Char"
vbzZKcjvNvXVGjXlNpm DoubleType  = fVjGOpLGXlqw "Double"
vbzZKcjvNvXVGjXlNpm WorldType   = fVjGOpLGXlqw "%World"

export
yYiIpchkXxucjiIzVkyDBc : TypeInfo
yYiIpchkXxucjiIzVkyDBc = fVjGOpLGXlqw "Type"

export
lBUigVVdDBanLKYICsc : TypeInfo -> TTImp
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Int"    ) [] [] = yJBCPcZ $ PrT IntType
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Integer") [] [] = yJBCPcZ $ PrT IntegerType
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Int8"   ) [] [] = yJBCPcZ $ PrT Int8Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Int16"  ) [] [] = yJBCPcZ $ PrT Int16Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Int32"  ) [] [] = yJBCPcZ $ PrT Int32Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Int64"  ) [] [] = yJBCPcZ $ PrT Int64Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Bits8"  ) [] [] = yJBCPcZ $ PrT Bits8Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Bits16" ) [] [] = yJBCPcZ $ PrT Bits16Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Bits32" ) [] [] = yJBCPcZ $ PrT Bits32Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Bits64" ) [] [] = yJBCPcZ $ PrT Bits64Type
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "String" ) [] [] = yJBCPcZ $ PrT StringType
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Char"   ) [] [] = yJBCPcZ $ PrT CharType
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Double" ) [] [] = yJBCPcZ $ PrT DoubleType
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "%World" ) [] [] = yJBCPcZ $ PrT WorldType
lBUigVVdDBanLKYICsc $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic "Type"   ) [] [] = sCAT
lBUigVVdDBanLKYICsc th = bDx th.qzYM

export
jtgaKKwkFbEmGm : TypeInfo -> Bool
jtgaKKwkFbEmGm $ MkTypeInfo (NS (MkNS ["^gWfa^"]) $ UN $ Basic y) [] [] = True
jtgaKKwkFbEmGm _ = False
--jtgaKKwkFbEmGm = fqH . lPsBS . mBOrfZxXLdqrfaOUyNv

0 aNcOvgznQXtCCIMgJDUExX : (y : String) -> jtgaKKwkFbEmGm (fVjGOpLGXlqw y) = True
aNcOvgznQXtCCIMgJDUExX y = Refl
