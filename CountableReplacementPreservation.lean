import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Filtered

/-! Finite accessibility of the original replacement preserves the actual countable colimit. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w uD vD
namespace DaggerCountableReplacementPreservation

attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem preserves {C : Type w} [Category.{v} C] {D : Type uD} [Category.{vD} D]
    (R : C ⥤ D) [R.IsCardinalAccessible Cardinal.aleph0.{u}] :
    PreservesColimitsOfShape ℕ R := by
  have : IsCardinalFiltered ℕ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff ℕ).2 inferInstance
  exact R.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    Cardinal.aleph0.{u} ℕ

end DaggerCountableReplacementPreservation
