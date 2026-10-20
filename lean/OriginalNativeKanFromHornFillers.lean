import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Actual horn extensions and Mathlib's native Kan condition

Every one-dimensional horn in every simplicial set has its actual degenerate
edge extension. The construction reuses native horn extensionality and the
native constant-simplex map. The full positive-dimensional horn extension
condition then gives Mathlib's native fibrancy class, without a new Kan hypothesis.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalNativeKanFromHornFillers

noncomputable section

/-- Every actual one-dimensional horn extends by a native degenerate edge. -/
theorem one_horn_filler {X : SSet.{u}} (i : Fin 2) (φ : (Λ[1, i] : SSet.{u}) ⟶ X) :
    ∃ σ : (Δ[1] : SSet.{u}) ⟶ X, φ = Λ[1, i].ι ≫ σ := by
  let j : Fin 2 := if i = 0 then 1 else 0
  have hj : j ≠ i := by fin_cases i <;> decide
  let y : X.obj (op ⦋0⦌) := φ.app (op ⦋0⦌) (SSet.horn.face i j hj)
  refine ⟨SSet.const y, ?_⟩
  apply SSet.horn.hom_ext
  intro k hk
  have hkj : k = j := by fin_cases i <;> fin_cases k <;> simp_all [j]
  subst k
  change φ.app (op ⦋0⦌) (SSet.horn.face i j hj) =
    (SSet.const y).app (op ⦋0⦌) ((Λ[1, i].ι).app (op ⦋0⦌) (SSet.horn.face i j hj))
  have hid : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  simpa only [SSet.const_app, hid, op_id, FunctorToTypes.map_id_apply] using
    (show φ.app (op ⦋0⦌) (SSet.horn.face i j hj) = y from rfl)

/-- The exact extension condition on every positive-dimensional original native horn. -/
def hornFillers (X : SSet.{u}) : Prop :=
  ∀ (n : ℕ) (i : Fin (n + 2)) (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ X),
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ X, φ = Λ[n + 1, i].ι ≫ σ

/-- Actual extensions of all original horns imply the native Mathlib Kan fibrancy class. -/
theorem kanComplex_of_hornFillers {X : SSet.{u}} (hX : hornFillers X) : X.KanComplex := by
  change IsFibrant X
  rw [isFibrant_iff, fibration_iff]
  intro P Q f hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨i⟩⟩ := hi
  constructor
  intro φ _ _
  obtain ⟨σ, hσ⟩ := hX n i φ
  exact CommSq.HasLift.mk' ⟨σ, hσ.symm, Subsingleton.elim _ _⟩

end

end DaggerOriginalNativeKanFromHornFillers
