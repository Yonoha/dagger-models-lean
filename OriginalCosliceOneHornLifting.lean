import OriginalJoinedOneHornLifting

/-!
# Relative one-horn lifts retain the exact fixed prefix

The native ordinal-sum operator leaves restriction to the original prefix
unchanged. The source vertex of an actual coslice horn therefore forces the
joined lift to have the same prefix simplex. This produces a lift into the
original fixed-prefix coslice, with the original boundary and horn equations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinalJoinLeft
open DaggerOriginalSimplexCoslice
open DaggerOriginalJoinedHornPrefix
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedOneHornLifting

universe u

namespace DaggerOriginalCosliceOneHornLifting

noncomputable section

/-- Evaluating the original prefix commutes with every native joined operator, as an equality. -/
theorem prefix_operator_eq {X : SSet.{u}} (k : SimplexCategory)
    {m n : SimplexCategory} (α : m ⟶ n) (s : (joinedPresheaf k X).obj (op n)) :
    X.map (AugmentedSimplexCategory.inl' k m).op ((joinedPresheaf k X).map α.op s) =
      X.map (AugmentedSimplexCategory.inl' k n).op s := by
  have h := congrArg (fun g ↦ g.op) (prefix_comp (k := k) α)
  change X.map (AugmentedSimplexCategory.inl' k m).op
    (X.map ((ordinalJoinLeft k).map α).op s) = _
  change ((ordinalJoinLeft k).map α).op ≫
    (AugmentedSimplexCategory.inl' k m).op = (AugmentedSimplexCategory.inl' k n).op at h
  calc
    _ = X.map (((ordinalJoinLeft k).map α).op ≫
        (AugmentedSimplexCategory.inl' k m).op) s :=
      (congrFun (X.map_comp _ _) s).symm
    _ = _ := congrFun (congrArg X.map h) s

/-- The literal relative (1,0)-horn lift lands in the same original fixed-prefix coslice. -/
theorem cosliceBoundaryRestriction_one_horn_lift {X : SSet.{u}}
    (hX : innerHornFillers X) (k : ℕ) (f : X.obj (op ⦋k⦌))
    (φ : (Λ[1, 0] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f)
    (β : (Δ[1] : SSet.{u}) ⟶ boundaryJoinedPresheaf k X)
    (w : φ ≫ cosliceBoundaryRestriction k X f = Λ[1, 0].ι ≫ β) :
    ∃ σ : (Δ[1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f,
      φ = Λ[1, 0].ι ≫ σ ∧ σ ≫ cosliceBoundaryRestriction k X f = β := by
  let A := prefixFiber ⦋k⦌ X f
  have wraw : (φ ≫ A.ι) ≫ joinedBoundaryRestriction k X = Λ[1, 0].ι ≫ β := by
    rw [Category.assoc]
    exact w
  obtain ⟨τ, hτhorn, hτboundary⟩ := joinedBoundaryRestriction_one_horn_lift hX k
    (φ ≫ A.ι) β wraw
  let r := (SSet.yonedaEquiv (X := joinedPresheaf ⦋k⦌ X) (n := ⦋1⦌)) τ
  let t := (SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ X f) (n := ⦋0⦌))
    (SSet.horn.ι (n := 0) 0 1 (by decide) ≫ φ)
  have hsource : SSet.stdSimplex.δ 1 ≫ τ =
      (SSet.horn.ι 0 1 (by decide) ≫ φ) ≫ A.ι := by
    rw [Category.assoc, hτhorn, ← Category.assoc, SSet.horn.ι_ι]
  have hs : (joinedPresheaf ⦋k⦌ X).map (SimplexCategory.δ (1 : Fin 2)).op r = t.val := by
    have hv := congrArg SSet.yonedaEquiv hsource
    have ho := yonedaEquiv_precomp_operator τ (SimplexCategory.δ (1 : Fin 2))
    change SSet.yonedaEquiv (SSet.stdSimplex.δ 1 ≫ τ) = _ at ho
    rw [ho, SSet.yonedaEquiv_comp] at hv
    exact hv
  have hr : r ∈ A.obj (op ⦋1⦌) := by
    have hp := prefix_operator_eq ⦋k⦌ (SimplexCategory.δ (1 : Fin 2)) r
    rw [hs] at hp
    change X.map (AugmentedSimplexCategory.inl' ⦋k⦌ ⦋1⦌).op r = f
    exact hp.symm.trans t.property
  let σ : (Δ[1] : SSet.{u}) ⟶ simplexCoslice ⦋k⦌ X f :=
    SSet.yonedaEquiv.symm ⟨r, hr⟩
  have hσ : σ ≫ A.ι = τ := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ X f) (n := ⦋1⦌))
      ((SSet.yonedaEquiv (X := simplexCoslice ⦋k⦌ X f) (n := ⦋1⦌)).symm ⟨r, hr⟩)).val = r
    rw [Equiv.apply_symm_apply]
  refine ⟨σ, ?_, ?_⟩
  · apply (cancel_mono A.ι).mp
    rw [Category.assoc, hσ]
    exact hτhorn
  · change σ ≫ (A.ι ≫ joinedBoundaryRestriction k X) = β
    rw [← Category.assoc, hσ]
    exact hτboundary

end

end DaggerOriginalCosliceOneHornLifting
