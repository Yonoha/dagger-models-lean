import TopCatModelCategory.SSet.Homotopy
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne

/-! Components of the actual internal Hom classify actual free simplicial homotopies. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFreeMappingComponents
noncomputable section

def component {K X : SSet.{u}} (f : K ⟶ X) : ((ihom K).obj X).π₀ :=
  SSet.π₀.mk (SSet.ihom₀Equiv.symm f)

theorem component_surjective (K X : SSet.{u}) :
    Function.Surjective (component (K := K) (X := X)) := by
  intro c
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective c
  refine ⟨SSet.ihom₀Equiv v, ?_⟩
  exact congrArg SSet.π₀.mk (SSet.ihom₀Equiv.symm_apply_apply v)

theorem component_eq_iff {K X : SSet.{u}} [IsFibrant X] (f g : K ⟶ X) :
    component f = component g ↔ Nonempty (SSet.Homotopy f g) := by
  change SSet.π₀.mk (SSet.ihom₀Equiv.symm f) =
    SSet.π₀.mk (SSet.ihom₀Equiv.symm g) ↔ _
  rw [SSet.KanComplex.π₀_mk_eq_π₀_mk_iff]
  exact ⟨fun ⟨h⟩ ↦ ⟨SSet.Homotopy.equiv.symm h⟩,
    fun ⟨h⟩ ↦ ⟨SSet.Homotopy.equiv h⟩⟩

theorem component_target {K X Y : SSet.{u}} (f : K ⟶ X) (g : X ⟶ Y) :
    SSet.mapπ₀ ((ihom K).map g) (component f) = component (f ≫ g) := rfl

theorem component_parameter {K L X : SSet.{u}} (u : L ⟶ K) (f : K ⟶ X) :
    SSet.mapπ₀ ((MonoidalClosed.pre u).app X) (component f) = component (u ≫ f) := by
  rw [component, SSet.mapπ₀_mk, component, SSet.ihom₀Equiv_symm_comp]

end
end DaggerNativeFreeMappingComponents
