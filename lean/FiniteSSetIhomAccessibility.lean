import NativeEndomorphismSimplexMaps
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! The actual internal Hom from a finite parameter preserves filtered colimits. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite MonoidalCategory Simplicial
open DaggerNativeEndomorphismSimplexMaps
universe u
namespace DaggerFiniteSSetIhomAccessibility
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

def evaluationIso (K : SSet.{u}) (n : ℕ) :
    ihom K ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌) ≅
      coyoneda.obj (op (K ⊗ Δ[n])) :=
  NatIso.ofComponents (fun X ↦ (simplexHomEquiv K X n).toIso) (by
    intro X Y f
    ext s
    exact simplexHomEquiv_post K f n s)

instance preservesFiltered (K : SSet.{u}) [K.Finite]
    (J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (ihom K) := by
  have : IsCardinalFiltered J Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff J).2 inferInstance
  apply preservesColimitsOfShape_of_evaluation (ihom K) J
  intro q
  have : (K ⊗ Δ[q.unop.len]).Finite := inferInstance
  have : (coyoneda.obj (op (K ⊗ Δ[q.unop.len]))).IsCardinalAccessible
      Cardinal.aleph0.{u} := inferInstance
  have : (ihom K ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj q).IsCardinalAccessible
      Cardinal.aleph0.{u} :=
    Functor.isCardinalAccessible_of_natIso (evaluationIso K q.unop.len).symm
      Cardinal.aleph0.{u}
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible _ Cardinal.aleph0.{u} J

instance finitelyAccessible (K : SSet.{u}) [K.Finite] :
    (ihom K).IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _ _ := by
    have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0.{u}
    infer_instance

theorem accessibleAtRegular (K : SSet.{u}) [K.Finite]
    (κ : Cardinal.{u}) [hκ : Fact κ.IsRegular] : (ihom K).IsCardinalAccessible κ :=
  (ihom K).isCardinalAccessible_of_le (κ := Cardinal.aleph0.{u}) hκ.out.aleph0_le

end
end DaggerFiniteSSetIhomAccessibility
