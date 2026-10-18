import NativeGroupoidChainExtension

/-! Inverse of the SAME original ordinary dagger, as a whole groupoid functor. -/
set_option autoImplicit false
open CategoryTheory DaggerModels
universe u
namespace DaggerNativeOrdinaryGroupoidSigma
noncomputable section
variable (C : Type u) [Groupoid.{u} C] [DaggerCategory C]

/-- The original dagger commutes with the original inverse. -/
theorem dagger_inv {x y : C} (f : x ⟶ y) :
    DaggerCategory.dagger (inv f) = inv (DaggerCategory.dagger f) := by
  apply IsIso.eq_inv_of_inv_hom_id
  rw [← DaggerCategory.dagger_comp, IsIso.hom_inv_id, DaggerCategory.dagger_id]

/-- This functor fixes objects and maps every arrow to exactly inverse original dagger. -/
def sigmaFunctor : C ⥤ C where
  obj x := x
  map f := inv (DaggerCategory.dagger f)
  map_id x := by rw [DaggerCategory.dagger_id, IsIso.inv_id]
  map_comp f g := by rw [DaggerCategory.dagger_comp, IsIso.inv_comp]

theorem sigma_involutive : sigmaFunctor C ⋙ sigmaFunctor C = 𝟭 C := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change inv (DaggerCategory.dagger (inv (DaggerCategory.dagger f))) = f
  rw [dagger_inv, DaggerCategory.dagger_involutive, IsIso.inv_inv]

end
end DaggerNativeOrdinaryGroupoidSigma
