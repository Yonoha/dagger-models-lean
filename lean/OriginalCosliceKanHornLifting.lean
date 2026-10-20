import OriginalJoinedKanHornLifting
import OriginalCosliceOneHornLifting

/-!
# All original fixed-prefix coslice horns over a Kan input

The all-index joined horn lift retains the same original prefix. Choose any
supplied coface distinct from the missing index to check that prefix. Both
original lifting equations survive the same actual coslice restriction.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedKanHornLifting
open DaggerOriginalCosliceOneHornLifting

universe u

namespace DaggerOriginalCosliceKanHornLifting

noncomputable section

/-- The actual fixed-prefix boundary restriction lifts all original horns over a Kan input. -/
theorem cosliceBoundaryRestriction_kan_horn_lift {X : SSet.{u}} [X.KanComplex]
    (k n : ℕ) (i : Fin (n + 2)) (f : X.obj (op ⦋k⦌))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ cosliceBoundaryRestriction k X f = Λ[n + 1, i].ι ≫ β) :
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f,
      φ = Λ[n + 1, i].ι ≫ σ ∧ σ ≫ cosliceBoundaryRestriction k X f = β := by
  let A := prefixFiber ⦋k⦌ X f
  have wraw : (φ ≫ A.ι) ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β := by
    rw [Category.assoc]
    exact w
  obtain ⟨τ, hτhorn, hτboundary⟩ := joinedBoundaryRestriction_kan_horn_lift k n i
    (φ ≫ A.ι) β wraw
  let j : Fin (n + 2) := if i = 0 then 1 else 0
  have hj : j ≠ i := by
    by_cases h : i = 0
    · subst i
      simp [j]
    · simp only [j, h, ↓reduceIte]
      exact Ne.symm h
  let r := (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n + 1⦌)) τ
  let t := (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ X f) (n := ⦋n⦌))
    (SSet.horn.ι i j hj ≫ φ)
  have hsource : SSet.stdSimplex.δ j ≫ τ = (SSet.horn.ι i j hj ≫ φ) ≫ A.ι := by
    rw [Category.assoc, hτhorn, ← Category.assoc, SSet.horn.ι_ι]
  have hs : (joinedPresheaf ⦋k⦌ X).map (SimplexCategory.δ j).op r = t.val := by
    have hv := congrArg SSet.yonedaEquiv hsource
    have ho := yonedaEquiv_precomp_operator τ (SimplexCategory.δ j)
    change SSet.yonedaEquiv (SSet.stdSimplex.δ j ≫ τ) = _ at ho
    rw [ho, SSet.yonedaEquiv_comp] at hv
    exact hv
  have hr : r ∈ A.obj (op ⦋n + 1⦌) := by
    have hp := prefix_operator_eq ⦋k⦌ (SimplexCategory.δ j) r
    rw [hs] at hp
    change X.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n + 1⦌).op r = f
    exact hp.symm.trans t.property
  let σ : (Δ[n + 1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f :=
    SSet.yonedaEquiv.symm ⟨r, hr⟩
  have hσ : σ ≫ A.ι = τ := by
    apply (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋n + 1⦌)).injective
    rw [SSet.yonedaEquiv_comp]
    change ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ X f) (n := ⦋n + 1⦌))
      ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ X f) (n := ⦋n + 1⦌)).symm ⟨r, hr⟩)).val = r
    rw [Equiv.apply_symm_apply]
  refine ⟨σ, ?_, ?_⟩
  · apply (cancel_mono A.ι).mp
    rw [Category.assoc, hσ]
    exact hτhorn
  · change σ ≫ (A.ι ≫ joinedBoundaryRestriction k X) = β
    rw [← Category.assoc, hσ]
    exact hτboundary

end

end DaggerOriginalCosliceKanHornLifting
