import OriginalJoinedLeftHornLifting
import OriginalCosliceOneHornLifting

/-!
# All relative left-horn lifts in the original fixed-prefix coslice

Choose the final supplied coface of a nonfinal horn. It belongs to the same
original prefix fiber. Prefix evaluation is invariant under every native
joined operator, so the full joined lift has exactly the same prefix. Its
restriction to that actual coslice retains both original lifting equations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedLeftHornLifting
open DaggerOriginalCosliceOneHornLifting

universe u

namespace DaggerOriginalCosliceLeftHornLifting

noncomputable section

/-- The actual fixed-prefix boundary restriction lifts all original nonfinal horns. -/
theorem cosliceBoundaryRestriction_left_horn_lift {X : SSet.{u}} (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) (f : X.obj (op ⦋k⦌))
    (φ : (Λ[n + 1, i] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f)
    (β : (Δ[n + 1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ cosliceBoundaryRestriction k X f = Λ[n + 1, i].ι ≫ β) :
    ∃ σ : (Δ[n + 1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f,
      φ = Λ[n + 1, i].ι ≫ σ ∧ σ ≫ cosliceBoundaryRestriction k X f = β := by
  let A := prefixFiber ⦋k⦌ X f
  have wraw : (φ ≫ A.ι) ≫ joinedBoundaryRestriction k X = Λ[n + 1, i].ι ≫ β := by
    rw [Category.assoc]
    exact w
  obtain ⟨τ, hτhorn, hτboundary⟩ := joinedBoundaryRestriction_left_horn_lift hX k n i hi
    (φ ≫ A.ι) β wraw
  let j := Fin.last (n + 1)
  have hj : j ≠ i := ne_of_gt hi
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

end DaggerOriginalCosliceLeftHornLifting
