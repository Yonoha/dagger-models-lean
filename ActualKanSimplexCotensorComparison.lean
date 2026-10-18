import ActualKanCotensorParameterWeakEquivalences
import NativeContractibleSimplexParameter

/-! Standard-simplex constants and their literal original-Q singular images are weak. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalFixedObjectCotensorPoints DaggerSSetGluing
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualKanCotensorParameterWeakEquivalences
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualKanSimplexCotensorComparison
noncomputable section

/-- The previously constructed raw simplex contraction gives the actual terminal weakness. -/
theorem simplex_toUnit_GW (n : ℕ) : GW (toUnit (Δ[n] : SSet.{u})) := by
  have : WeakEquivalence (snd (Δ[n] : SSet.{u}) (𝟙_ SSet.{u})) :=
    DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence n _
  have h : (ρ_ (Δ[n] : SSet.{u})).inv ≫ snd Δ[n] (𝟙_ SSet.{u}) =
      toUnit (Δ[n] : SSet.{u}) :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← h]
  infer_instance

/-- The unchanged constant map into a standard-simplex cotensor is geometrically weak. -/
theorem simplex_constants_GW (X : SSet.{u}) [X.KanComplex] (n : ℕ) :
    GW (constantHom (Δ[n] : SSet.{u}) X) :=
  constantHom_GW Δ[n] X (simplex_toUnit_GW n)

/-- Both targets are Kan, so the verified original-Q Brown theorem preserves this map. -/
theorem singular_simplex_constants_GW (X : SSet.{u}) [X.KanComplex] (n : ℕ) :
    GW (singular.{u}.map (constantHom (Δ[n] : SSet.{u}) X)) :=
  DaggerActualQSingularFibrantWeakEquivalences.singular_GW _ (simplex_constants_GW X n)

end
end DaggerActualKanSimplexCotensorComparison
