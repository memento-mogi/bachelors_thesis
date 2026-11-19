nat : Type

Ki : Type
Ty(TyVar) : Type
Tm(TmVar) : Type

KiStar : Ki
KiPi : Ty -> (bind Tm in Ki) -> Ki

TyVar : nat -> Ty
TyPi : Ty -> (bind Tm in Ty) -> Ty
TyTmApp : Ty -> Tm -> Ty
TyUnit : Ty

TmAbs : Ty -> (bind Tm in Tm) -> Tm
TmApp : Tm -> Tm -> Tm
TmUnit : Tm
