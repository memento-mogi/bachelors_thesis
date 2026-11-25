ty : Type
tm : Type
list : Functor
nat : Type

TyArrow : ty -> ty -> ty
TyForall : (bind ty in ty) -> ty
TyProd : "list" (ty) -> ty
TySum : "list" (ty) -> ty
TyUnit : ty

TmAbs : ty -> (bind tm in tm) -> tm
TmApp : tm -> tm -> tm
TmTAbs : (bind ty in tm) -> tm
TmTApp : tm -> ty -> tm
TmTuple : "list" (tm) -> tm
TmProj : nat -> tm -> tm
TmInj: nat -> tm -> tm
TmCase : tm -> "list" (tm) -> tm 
TmUnit : tm