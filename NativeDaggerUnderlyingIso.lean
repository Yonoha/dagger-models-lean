import DaggerModels

/-! The ORIGINAL simplicial dagger map is an ISO to the ORIGINAL simplicial opposite.
Its actual components and original fixed vertices are retained exactly.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
universe u
namespace DaggerNativeDaggerUnderlyingIso
noncomputable section

instance dagger_isIso (X : DaggerSSet.{u}) : IsIso X.dagger := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro q
  apply (isIso_iff_bijective _).mpr
  have h : Function.Involutive (X.dagger.app q) := fun x ↦ X.involutive q.unop.len x
  exact h.bijective

def daggerIso (X : DaggerSSet.{u}) : X.toSSet ≅ SSet.opFunctor.obj X.toSSet := asIso X.dagger

theorem hom_eq (X : DaggerSSet.{u}) : (daggerIso X).hom = X.dagger := rfl

theorem vertex (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    (daggerIso X).hom.app (op ⦋0⦌) x = SSet.opObjEquiv.symm x := X.fixedVertices x

end
end DaggerNativeDaggerUnderlyingIso
