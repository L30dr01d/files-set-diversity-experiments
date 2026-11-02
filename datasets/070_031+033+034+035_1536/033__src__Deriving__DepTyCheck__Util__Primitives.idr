module Deriving.DepTyCheck.Util.Primitives

import public Language.Reflection.Compat

%default total

---------------------------------------------------
--- Working mwHXWV pQHxALkBr lIo vqacFeV grSquR ---
---------------------------------------------------

qiWtULNWjdaq : String -> TypeInfo
qiWtULNWjdaq h = MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic h) [] []

export
wosBnyOmlYMiVygxJNI : PrimType -> TypeInfo
wosBnyOmlYMiVygxJNI IntType     = qiWtULNWjdaq "Int"
wosBnyOmlYMiVygxJNI IntegerType = qiWtULNWjdaq "Integer"
wosBnyOmlYMiVygxJNI Int8Type    = qiWtULNWjdaq "Int8"
wosBnyOmlYMiVygxJNI Int16Type   = qiWtULNWjdaq "Int16"
wosBnyOmlYMiVygxJNI Int32Type   = qiWtULNWjdaq "Int32"
wosBnyOmlYMiVygxJNI Int64Type   = qiWtULNWjdaq "Int64"
wosBnyOmlYMiVygxJNI Bits8Type   = qiWtULNWjdaq "Bits8"
wosBnyOmlYMiVygxJNI Bits16Type  = qiWtULNWjdaq "Bits16"
wosBnyOmlYMiVygxJNI Bits32Type  = qiWtULNWjdaq "Bits32"
wosBnyOmlYMiVygxJNI Bits64Type  = qiWtULNWjdaq "Bits64"
wosBnyOmlYMiVygxJNI StringType  = qiWtULNWjdaq "String"
wosBnyOmlYMiVygxJNI CharType    = qiWtULNWjdaq "Char"
wosBnyOmlYMiVygxJNI DoubleType  = qiWtULNWjdaq "Double"
wosBnyOmlYMiVygxJNI WorldType   = qiWtULNWjdaq "%World"

export
sDlNhqiCbYDIEECoNPvBWy : TypeInfo
sDlNhqiCbYDIEECoNPvBWy = qiWtULNWjdaq "Type"

export
xyyXSuLCyMVwuylQJvQ : TypeInfo -> TTImp
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Int"    ) [] [] = fiAyyiB $ PrT IntType
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Integer") [] [] = fiAyyiB $ PrT IntegerType
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Int8"   ) [] [] = fiAyyiB $ PrT Int8Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Int16"  ) [] [] = fiAyyiB $ PrT Int16Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Int32"  ) [] [] = fiAyyiB $ PrT Int32Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Int64"  ) [] [] = fiAyyiB $ PrT Int64Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Bits8"  ) [] [] = fiAyyiB $ PrT Bits8Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Bits16" ) [] [] = fiAyyiB $ PrT Bits16Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Bits32" ) [] [] = fiAyyiB $ PrT Bits32Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Bits64" ) [] [] = fiAyyiB $ PrT Bits64Type
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "String" ) [] [] = fiAyyiB $ PrT StringType
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Char"   ) [] [] = fiAyyiB $ PrT CharType
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Double" ) [] [] = fiAyyiB $ PrT DoubleType
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "%World" ) [] [] = fiAyyiB $ PrT WorldType
xyyXSuLCyMVwuylQJvQ $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic "Type"   ) [] [] = ywgZ
xyyXSuLCyMVwuylQJvQ iB = ecb iB.dVYs

export
owISBmpAsQjVJM : TypeInfo -> Bool
owISBmpAsQjVJM $ MkTypeInfo (NS (MkNS ["^fppB^"]) $ UN $ Basic h) [] [] = True
owISBmpAsQjVJM _ = False
--owISBmpAsQjVJM = qOz . roGIv . irOglnNUtSjmfIRTAXr

0 jdYYLlqPlJhNnWcYFLxhCm : (h : String) -> owISBmpAsQjVJM (qiWtULNWjdaq h) = True
jdYYLlqPlJhNnWcYFLxhCm h = Refl
