import OriginalCounitRightConeQCommonBaseFaceReconciled
import OriginalCounitRightConeQCofaceInjectionReconciled

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeQCommonBaseFace
open DaggerOriginalCounitRightConeQCofaceInjection

universe u

namespace DaggerOriginalCounitRightConeQCommonBaseRetractionFactor

noncomputable section

/-- The explicit common old face is a composite of two genuine cofaces. -/
theorem commonBaseHom_as_two_cofaces (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    ∃ h : Fin (n + 2),
      commonBaseHom n i j hij =
        SimplexCategory.δ h ≫ SimplexCategory.δ j := by
  let α := commonBaseHom n i j hij
  let γ := SimplexCategory.factor_δ α j
  have hnot (v : Fin (n + 1)) : α.toOrderHom v ≠ j :=
    ((commonBaseHom_vertex_range n i j hij (α.toOrderHom v)).1
      ⟨v, rfl⟩).2
  have hfactor : γ ≫ SimplexCategory.δ j = α :=
    SimplexCategory.factor_δ_spec α j hnot
  haveI : Mono α := by
    apply SimplexCategory.mono_iff_injective.mpr
    intro v w hvw
    apply (commonBaseOrderIso n i j hij).injective
    exact Subtype.ext hvw
  haveI : Mono (γ ≫ SimplexCategory.δ j) := by
    rw [hfactor]
    infer_instance
  haveI : Mono γ := CategoryTheory.mono_of_mono γ (SimplexCategory.δ j)
  obtain ⟨h, hγ⟩ := SimplexCategory.eq_δ_of_mono γ
  refine ⟨h, ?_⟩
  change α = SimplexCategory.δ h ≫ SimplexCategory.δ j
  rw [← hfactor, hγ]

/-- Retraction of the common old face as a composite of the two actual
degeneracy retractions, without a new finite-order construction. -/
theorem commonBaseHom_has_retraction (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    ∃ r : ⦋n + 2⦌ ⟶ ⦋n⦌,
      commonBaseHom n i j hij ≫ r = 𝟙 ⦋n⦌ := by
  obtain ⟨h, hα⟩ := commonBaseHom_as_two_cofaces n i j hij
  obtain ⟨rj, hrj⟩ := coface_has_retraction (n + 1) j
  obtain ⟨rh, hrh⟩ := coface_has_retraction n h
  refine ⟨rj ≫ rh, ?_⟩
  rw [hα]
  calc
    (SimplexCategory.δ h ≫ SimplexCategory.δ j) ≫ (rj ≫ rh) =
        SimplexCategory.δ h ≫
          ((SimplexCategory.δ j ≫ rj) ≫ rh) := by
      simp only [Category.assoc]
    _ = 𝟙 ⦋n⦌ := by rw [hrj, Category.id_comp, hrh]

end

end DaggerOriginalCounitRightConeQCommonBaseRetractionFactor
