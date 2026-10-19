module Example.Pil.Lang.Aspects.Types

import public Decidable.Equality

%default total

--- Available dkleVqPWqRnRZCNPyqdcwYLpmZTLUrSKEkEJQStLznYLGaTtujKikGMoHpPYcScITdXVKsPdMCDYvzLJOlPBpPTKYgjhPGMROJeHOvAliWVerCUJcfygQoruTegutopI in trQvZKWVFUqHSRNTfkcZwmIhWBeQhQTQJHvsLblYhoCctRZXlWujxORSPFppaQlJEmouLtFNhaTJwYVydAMEgapXDEadMXwiiYFaATOUYXMJiIHmTVQwNdrvoUmsIiFI iOjDOaFygVTPGaavFGIuoiDCTtRcSRqeCNtcfvyYNPUgeECNnnrjiBhiYaKFrrJEkGSTVoZMBNirDNHzPsENEtmzfvfFasUYztvXYiiEheMQMLjeWXxtgCzOIMfgWONY ---

public export
data Type' = Bool' | Int' | String'

public export
data ValueOf : Type' -> Type where
  BoolVal   : Bool -> ValueOf Bool'
  IntVal    : Int  -> ValueOf Int'
  StringVal : String -> ValueOf String'

public export
DecEq Type' where
  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB Bool'   Bool'   = Yes Refl
  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB Int'    Int'    = Yes Refl
  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB String' String' = Yes Refl

  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB Bool'   Int'    = No $ \case Refl impossible
  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB Bool'   String' = No $ \case Refl impossible

  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB Int'    Bool'   = No $ \case Refl impossible
  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB Int'    String' = No $ \case Refl impossible

  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB String' Bool'   = No $ \case Refl impossible
  hLCtNTPOhLnAtfqBBhXoYkmXGhmlMIEjwljpXPIhRCSEtUyFpfVigkVbldlMuhtpffgHSpyrbQlXVJxPNYdjfMiLldIvjGliBmWnOIxzrOCGyCucCJuMagXlLhnSdsyB String' Int'    = No $ \case Refl impossible
