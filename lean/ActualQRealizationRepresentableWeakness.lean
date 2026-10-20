import OriginalCounitRightConeQRealizationAdjunctionReconciled
import ActualCounitRightConeQHomotopicalDiagram
import OriginalCounitRightConeQCofaceInjectionReconciled

/-! Weak representable maps of the original Q realization. -/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open DaggerOriginalCounitRightConeQFunctor DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQRealizationRepresentableWeakness

noncomputable section

instance unit_isIso : IsIso realizationUnit.{u} := by
  dsimp [realizationUnit, realization]
  infer_instance

/-- The actual Kan extension sends each standard simplex to the original Q in that degree. -/
def representableIso (n : SimplexCategory) :
    realization.{u}.obj (uliftYoneda.{u}.obj n) ≅ QFunctor.{u}.obj n :=
  (asIso (realizationUnit.app n)).symm

/-- Realization of every representable has weak terminal collapse. -/
theorem representable_toUnit_GW (n : SimplexCategory) :
    GW (toUnit (realization.{u}.obj (uliftYoneda.{u}.obj n))) := by
  have : WeakEquivalence (toUnit (QFunctor.{u}.obj n)) :=
    (weakEquivalence_iff_GW _).2
      (DaggerActualCounitRightConeQHomotopicalDiagram.object_toUnit_GW n)
  have h : (representableIso.{u} n).hom ≫ toUnit (QFunctor.obj n) =
      toUnit (realization.obj (uliftYoneda.obj n)) := isTerminalTensorUnit.hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← h]
  infer_instance

/-- Every literal simplex operator is sent to a weak map by the original realization. -/
theorem operator_GW {m n : SimplexCategory} (f : m ⟶ n) :
    GW (realization.{u}.map (uliftYoneda.{u}.map f)) := by
  have : WeakEquivalence (QFunctor.{u}.map f) := (weakEquivalence_iff_GW _).2
    (DaggerActualCounitRightConeQHomotopicalDiagram.transition_GW f)
  have : WeakEquivalence
      (realizationUnit.{u}.app m ≫ realization.map (uliftYoneda.map f)) := by
    have h := realizationUnit.{u}.naturality f
    change QFunctor.map f ≫ realizationUnit.app n =
      realizationUnit.app m ≫ realization.map (uliftYoneda.map f) at h
    rw [← h]
    infer_instance
  exact (weakEquivalence_iff_GW _).1
    (weakEquivalence_of_precomp (realizationUnit.{u}.app m)
      (realization.map (uliftYoneda.map f)))

/-- The exact naturality square conjugates a realized operator to the original Q operator. -/
theorem operator_eq {m n : SimplexCategory} (f : m ⟶ n) :
    realization.{u}.map (uliftYoneda.{u}.map f) =
      (representableIso.{u} m).hom ≫ QFunctor.map f ≫ (representableIso n).inv := by
  have h := realizationUnit.{u}.naturality f
  change QFunctor.map f ≫ realizationUnit.app n =
    realizationUnit.app m ≫ realization.map (uliftYoneda.map f) at h
  dsimp [representableIso]
  rw [h]
  simp

/-- Each realized coface is monic, using the original degeneracy retraction. -/
theorem coface_mono (k : ℕ) (i : Fin (k + 2)) :
    Mono (realization.{u}.map (uliftYoneda.{u}.map (SimplexCategory.δ i))) := by
  rw [operator_eq]
  have := DaggerOriginalCounitRightConeQCofaceInjection.Qcoface_mono.{u} k i
  infer_instance

/-- Every realized coface is a trivial cofibration in the actual Kan-Quillen model. -/
theorem coface_trivialCofibration (k : ℕ) (i : Fin (k + 2)) :
    trivialCofibrations SSet.{u}
      (realization.{u}.map (uliftYoneda.{u}.map (SimplexCategory.δ i))) := by
  have := coface_mono.{u} k i
  have : Cofibration (realization.{u}.map (uliftYoneda.{u}.map (SimplexCategory.δ i))) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  have : WeakEquivalence
      (realization.{u}.map (uliftYoneda.{u}.map (SimplexCategory.δ i))) :=
    (weakEquivalence_iff_GW _).2 (operator_GW (SimplexCategory.δ i))
  exact mem_trivialCofibrations _

end
end DaggerActualQRealizationRepresentableWeakness
