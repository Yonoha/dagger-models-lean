import OriginalJoinedHornGeometry

/-!
# Joined inner-horn fillers retain the exact fixed prefix simplex

The native left ordinal block lies in the joined horn, because the nonfinal
omitted right-block vertex is distinct from the last vertex. The exact horn
extension equation therefore forces the prefix to be unchanged. Evaluation
on the original Yoneda simplex puts the filler in the actual simplex coslice.
All maps, simplices and restrictions are original, in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornGeometry
open DaggerOriginalOrdinaryKanCoreInnerHorns

universe u

namespace DaggerOriginalJoinedHornPrefix

noncomputable section

/-- The native original left block is a simplex of the joined horn. -/
theorem prefix_mem_joinedHorn (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    SSet.stdSimplex.objEquiv.symm (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌) ∈
      (Λ[k + n + 1, suffixIndex k n i] :
        (Δ[k + n + 1] : SSet.{u}).Subcomplex).obj (op ⦋k⦌) := by
  change Set.range (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌).toOrderHom ∪
    {suffixIndex k n i} ≠ Set.univ
  intro h
  have hlast := Set.eq_univ_iff_forall.mp h (suffixIndex k n (Fin.last n))
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hlast
  rcases hlast with ⟨j, hj⟩ | hj
  · rw [← prefixIndex_eq_native] at hj
    exact prefixIndex_ne_suffixIndex k n j (Fin.last n) hj
  · have hji := suffixIndex_injective k n hj
    have hn : (Fin.last n : Fin (n + 1)) ≠ i := ne_of_gt hi
    exact hn hji

/-- The literal original left block inclusion into the actual joined horn. -/
def prefixHornInclusion (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    (Δ[k] : SSet.{u}) ⟶ (Λ[k + n + 1, suffixIndex k n i] : SSet.{u}) :=
  SSet.yonedaEquiv.symm ⟨SSet.stdSimplex.objEquiv.symm
    (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌), prefix_mem_joinedHorn k n i hi⟩

/-- Following the original prefix inclusion by the horn inclusion is the native block map. -/
theorem prefixHornInclusion_comp (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) :
    prefixHornInclusion.{u} k n i hi ≫ Λ[k + n + 1, suffixIndex k n i].ι =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  change (SSet.stdSimplex.objEquiv.symm
    (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌)) = _
  rfl

/-- Precomposing with the actual simplex operator evaluates that operator on the same simplex. -/
theorem yonedaEquiv_precomp_operator {X : SSet.{u}} {k m : ℕ}
    (σ : (Δ[m] : SSet.{u}) ⟶ X) (α : ⦋k⦌ ⟶ ⦋m⦌) :
    SSet.yonedaEquiv (SSet.stdSimplex.map α ≫ σ) = X.map α.op (SSet.yonedaEquiv σ) := by
  rw [SSet.yonedaEquiv_comp]
  change σ.app (op ⦋k⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌ ≫ α)) = _
  rw [Category.id_comp]
  exact simplex_app_operator σ α

/-- The actual joined horn filler preserves the given original prefix map exactly. -/
theorem joined_horn_filling_fixed_prefix (X : SSet.{u}) (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n)
    (f : (Δ[k] : SSet.{u}) ⟶ X)
    (σ₀ : (Λ[k + n + 1, suffixIndex k n i] : SSet.{u}) ⟶ X)
    (hf : prefixHornInclusion k n i hi ≫ σ₀ = f) :
    ∃ σ : (Δ[k + n + 1] : SSet.{u}) ⟶ X,
      σ₀ = Λ[k + n + 1, suffixIndex k n i].ι ≫ σ ∧
      SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋n⦌) ≫ σ = f := by
  have hinner := suffixIndex_inner k n i hi
  obtain ⟨σ, hσ⟩ := hX hinner.1 hinner.2 σ₀
  refine ⟨σ, hσ, ?_⟩
  rw [← prefixHornInclusion_comp k n i hi, Category.assoc, ← hσ]
  exact hf

/-- Evaluating that same original filler gives an actual simplex of the fixed-prefix coslice. -/
theorem coslice_simplex_of_joined_horn (X : SSet.{u}) (hX : innerHornFillers X)
    (k n : ℕ) (i : Fin (n + 1)) (hi : i < Fin.last n) (f : X.obj (op ⦋k⦌))
    (σ₀ : (Λ[k + n + 1, suffixIndex k n i] : SSet.{u}) ⟶ X)
    (hf : prefixHornInclusion k n i hi ≫ σ₀ = SSet.yonedaEquiv.symm f) :
    ∃ s : (simplexCoslice ⦋k⦌ X f).obj (op ⦋n⦌),
      σ₀ = Λ[k + n + 1, suffixIndex k n i].ι ≫ SSet.yonedaEquiv.symm s.val := by
  obtain ⟨σ, hσ, hp⟩ := joined_horn_filling_fixed_prefix X hX k n i hi
    (SSet.yonedaEquiv.symm f) σ₀ hf
  have hv := congrArg SSet.yonedaEquiv hp
  rw [yonedaEquiv_precomp_operator, Equiv.apply_symm_apply] at hv
  refine ⟨⟨SSet.yonedaEquiv (X := X) σ, hv⟩, ?_⟩
  change σ₀ = Λ[k + n + 1, suffixIndex k n i].ι ≫
    (SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)).symm
      ((SSet.yonedaEquiv (X := X) (n := ⦋k + n + 1⦌)) σ)
  rw [Equiv.symm_apply_apply]
  exact hσ

end

end DaggerOriginalJoinedHornPrefix
