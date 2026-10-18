import OriginalStandardSimplexReversal
import OriginalSimplicialSubcomplexOpposite

/-!
# Exact native horn reversal with the original ambient inclusion

Reversal sends the literal range-complement predicate of the original horn to
the horn at the reversed vertex. Native subcomplex lifts give an isomorphism
on the actual horns. Both inclusion equations retain the exact original
standard-simplex reversal maps, in every dimension and universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalStandardSimplexReversal DaggerOriginalSimplicialSubcomplexOpposite

universe u

namespace DaggerOriginalHornReversal

noncomputable section

/-- Native operator reversal keeps the exact original horn predicate at the reversed index. -/
theorem horn_mem_reverse {n : ℕ} (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (s : (Δ[n] : SSet.{u}).obj q) (hs : s ∈ (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).obj q) :
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s)) ∈
      (Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).obj q := by
  change Set.range (SSet.stdSimplex.objEquiv s).toOrderHom ∪ {i} ≠ Set.univ at hs
  change Set.range (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv s)).toOrderHom ∪
    {i.rev} ≠ Set.univ
  intro h
  apply hs
  apply Set.eq_univ_iff_forall.mpr
  intro j
  rcases Set.eq_univ_iff_forall.mp h j.rev with ⟨a, ha⟩ | hj
  · left
    refine ⟨a.rev, ?_⟩
    simpa only [SimplexCategory.rev_map_apply, Fin.rev_rev] using congrArg Fin.rev ha
  · right
    change j = i
    have hj' : j.rev = i.rev := hj
    simpa only [Fin.rev_rev] using congrArg Fin.rev hj'

/-- The actual reversed ambient inclusion has its range in the actual reversed-index horn. -/
theorem hornReversalHom_range (n : ℕ) (i : Fin (n + 1)) :
    SSet.Subcomplex.range (SSet.opFunctor.map
      (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι ≫ standardSimplexReversalHom n) ≤
        Λ[n, i.rev] := by
  intro q s hs
  obtain ⟨t, rfl⟩ := hs
  exact horn_mem_reverse i (SSet.opObjEquiv t).val (SSet.opObjEquiv t).property

/-- The original opposite horn maps into the native horn at the reversed index. -/
def hornReversalHom (n : ℕ) (i : Fin (n + 1)) :
    (Λ[n, i] : SSet.{u}).op ⟶ (Λ[n, i.rev] : SSet.{u}) :=
  SSet.Subcomplex.lift (SSet.opFunctor.map
    (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι ≫ standardSimplexReversalHom n)
      (hornReversalHom_range n i)

/-- The forward map commutes with the exact original ambient inclusion. -/
theorem hornReversalHom_comp_ι (n : ℕ) (i : Fin (n + 1)) :
    hornReversalHom.{u} n i ≫ Λ[n, i.rev].ι =
      SSet.opFunctor.map (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι ≫
        standardSimplexReversalHom n := SSet.Subcomplex.lift_ι _ _

/-- The reversed-index horn maps back into the actual opposite original horn. -/
theorem hornReversalInv_range (n : ℕ) (i : Fin (n + 1)) :
    SSet.Subcomplex.range ((Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι ≫
      standardSimplexReversalInv n) ≤
        oppositeSubcomplex (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex) := by
  intro q s hs
  obtain ⟨t, rfl⟩ := hs
  have h := horn_mem_reverse i.rev t.val t.property
  simpa only [Fin.rev_rev] using h

/-- The inverse lands in the exact original native opposite horn. -/
def hornReversalInv (n : ℕ) (i : Fin (n + 1)) :
    (Λ[n, i.rev] : SSet.{u}) ⟶ (Λ[n, i] : SSet.{u}).op :=
  liftToOpposite (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex)
    ((Λ[n, i.rev] : (Δ[n] : SSet.{u}).Subcomplex).ι ≫ standardSimplexReversalInv n)
      (hornReversalInv_range n i)

/-- The inverse map commutes with the same original opposite inclusion. -/
theorem hornReversalInv_comp_ι (n : ℕ) (i : Fin (n + 1)) :
    hornReversalInv.{u} n i ≫
      SSet.opFunctor.map (Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).ι =
        Λ[n, i.rev].ι ≫ standardSimplexReversalInv n := liftToOpposite_comp_ι _ _ _

/-- The actual original horn reverses to the native horn at the reversed vertex by an iso. -/
def hornReversalIso (n : ℕ) (i : Fin (n + 1)) :
    (Λ[n, i] : SSet.{u}).op ≅ (Λ[n, i.rev] : SSet.{u}) where
  hom := hornReversalHom n i
  inv := hornReversalInv n i
  hom_inv_id := by
    ext q s
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (SimplexCategory.rev.map
      (SSet.stdSimplex.objEquiv (SSet.opObjEquiv s).val)) =
        SSet.stdSimplex.objEquiv (SSet.opObjEquiv s).val
    exact reverse_operator_twice _
  inv_hom_id := by
    ext q s
    apply Subtype.ext
    apply SSet.stdSimplex.objEquiv.injective
    change SimplexCategory.rev.map (SimplexCategory.rev.map
      (SSet.stdSimplex.objEquiv s.val)) = SSet.stdSimplex.objEquiv s.val
    exact reverse_operator_twice _

end

end DaggerOriginalHornReversal
