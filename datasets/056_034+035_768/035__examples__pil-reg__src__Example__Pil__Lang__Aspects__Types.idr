module Example.Pil.Lang.Aspects.Types

import public Decidable.Equality

%default total

--- Available fyCZvPAJNCDhVZvFdDHmmCkbPupzZWxmyyYtytbeScRLUnDqtCusrpItlFGtfwvzOCwdNCBjHVvdaURuxrIsuzSXTePCJnoXStZMLOcrErUeghOEctAeGLAJEJSNzdTl in yFGlcukoTEbVZqZUWqVKbcMFZuGBYFHYPlTNawOEUAhXYdMMXnZnKpupLDZfiBLUGknAPVRfWrtOpdshKVAJBWXMBzpylHPfmNOVHuPwKPSYHXZrVaRuRSXkhCIvBVdQ eTJBZnikEVVQsYjbbmltMfGPIfODIpjGFNXnyQUlEkczdkRhlerESSAuJPtPrNqfOcYlyBiwUjtVZoYyJXtXoBJradMjoDLAPSarvgGlXhKfSaoEYlyQFclVyPmvOZHx ---

public export
data Type' = Bool' | Int' | String'

public export
data ValueOf : Type' -> Type where
  BoolVal   : Bool -> ValueOf Bool'
  IntVal    : Int  -> ValueOf Int'
  StringVal : String -> ValueOf String'

public export
DecEq Type' where
  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys Bool'   Bool'   = Yes Refl
  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys Int'    Int'    = Yes Refl
  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys String' String' = Yes Refl

  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys Bool'   Int'    = No $ \case Refl impossible
  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys Bool'   String' = No $ \case Refl impossible

  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys Int'    Bool'   = No $ \case Refl impossible
  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys Int'    String' = No $ \case Refl impossible

  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys String' Bool'   = No $ \case Refl impossible
  mQSXzJuBVQmayGuliPpEFZvMfhpcYpeRaAndtlYXsgWYwAvqnINfagzmblLiTYtgNeprEWYUhZgblmDjtJcIeEgKqDizFExFtLwNYjiTsCdakVTZhszwQLgXQHawNdys String' Int'    = No $ \case Refl impossible
