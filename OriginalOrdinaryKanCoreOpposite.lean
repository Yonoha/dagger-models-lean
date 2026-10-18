import OriginalHomotopyCategoryOppositeComparison
import OriginalOrdinaryKanCoreFunctor
import OriginalSimplicialSubcomplexOpposite

/-!
# The original core candidate commutes with simplicial reversal

The comparison uses the same homotopy-category unit and the same core candidate.
The reverse membership implication follows from the native double-opposite
isomorphism and the already proved functoriality, without replacing the core.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalHomotopyCategoryOppositeComparison
open DaggerOriginalSimplicialSubcomplexOpposite

universe u

namespace DaggerOriginalOrdinaryKanCoreOpposite

noncomputable section

/-- Every simplex in the original core remains in the core after simplicial reversal. -/
theorem mem_ordinaryCoreCandidate_op (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (s : X.obj q) (hs : s ∈ (ordinaryCoreCandidate X).obj q) :
    SSet.opObjEquiv.symm s ∈ (ordinaryCoreCandidate X.op).obj q := by
  apply (mem_ordinaryCoreCandidate_iff_edges_iso X.op q _).mpr
  intro α
  rw [SSet.op_map]
  apply edgeIsInvertible_op
  exact (mem_ordinaryCoreCandidate_iff_edges_iso X q s).mp hs (SimplexCategory.rev.map α)

/-- Core membership is transported through a map using the proved inclusion equation. -/
theorem mem_ordinaryCoreCandidate_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (q : SimplexCategoryᵒᵖ) (s : X.obj q) (hs : s ∈ (ordinaryCoreCandidate X).obj q) :
    f.app q s ∈ (ordinaryCoreCandidate Y).obj q := by
  let cs : (ordinaryCoreCandidate X : SSet.{u}).obj q := ⟨s, hs⟩
  have h := ((ordinaryCoreCandidateMap f).app q cs).property
  have hv := congrArg
    (fun k : (ordinaryCoreCandidate X : SSet.{u}) ⟶ Y ↦ k.app q cs)
    (ordinaryCoreCandidateMap_comp_ι f)
  change ((ordinaryCoreCandidateMap f).app q cs).val = f.app q s at hv
  rw [← hv]
  exact h

/-- Reverse membership is recovered through the exact native double-opposite isomorphism. -/
theorem mem_ordinaryCoreCandidate_unop (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (s : X.op.obj q) (hs : s ∈ (ordinaryCoreCandidate X.op).obj q) :
    SSet.opObjEquiv s ∈ (ordinaryCoreCandidate X).obj q := by
  have ht := mem_ordinaryCoreCandidate_op X.op q s hs
  have h := mem_ordinaryCoreCandidate_map (SSet.opFunctorCompOpFunctorIso.hom.app X) q
    (SSet.opObjEquiv.symm s) ht
  rw [SSet.opFunctorCompOpFunctorIso_hom_app_app] at h
  exact h

/-- Exact core membership is invariant under simplicial reversal in all degrees. -/
theorem mem_ordinaryCoreCandidate_op_iff (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (s : X.obj q) :
    SSet.opObjEquiv.symm s ∈ (ordinaryCoreCandidate X.op).obj q ↔
      s ∈ (ordinaryCoreCandidate X).obj q := by
  constructor
  · intro hs
    exact mem_ordinaryCoreCandidate_unop X q (SSet.opObjEquiv.symm s) hs
  · exact mem_ordinaryCoreCandidate_op X q s

/-- The exact opposite inclusion has its range in the core of the reversed simplicial set. -/
theorem coreOppositeComparison_range (X : SSet.{u}) :
    SSet.Subcomplex.range (SSet.opFunctor.map (ordinaryCoreCandidate X).ι) ≤
      ordinaryCoreCandidate X.op := by
  intro q s hs
  obtain ⟨t, rfl⟩ := hs
  exact mem_ordinaryCoreCandidate_op X q (SSet.opObjEquiv t).val
    (SSet.opObjEquiv t).property

/-- A natural comparison on the actual core subcomplexes. -/
def coreOppositeComparison (X : SSet.{u}) :
    (ordinaryCoreCandidate X : SSet.{u}).op ⟶ (ordinaryCoreCandidate X.op : SSet.{u}) :=
  SSet.Subcomplex.lift (SSet.opFunctor.map (ordinaryCoreCandidate X).ι)
    (coreOppositeComparison_range X)

/-- The exact reversed core lies in the native reversal of the original subcomplex. -/
theorem coreOppositeInclusion_range (X : SSet.{u}) :
    SSet.Subcomplex.range (ordinaryCoreCandidate X.op).ι ≤
      oppositeSubcomplex (ordinaryCoreCandidate X) := by
  intro q s hs
  obtain ⟨t, rfl⟩ := hs
  exact mem_ordinaryCoreCandidate_unop X q t.val t.property

/-- The inverse comparison keeps the exact underlying simplex and its original core predicate. -/
def coreOppositeComparisonInv (X : SSet.{u}) :
    (ordinaryCoreCandidate X.op : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}).op :=
  liftToOpposite (ordinaryCoreCandidate X) (ordinaryCoreCandidate X.op).ι
    (coreOppositeInclusion_range X)

/-- The comparison commutes with the original subcomplex inclusions. -/
theorem coreOppositeComparison_comp_ι (X : SSet.{u}) :
    coreOppositeComparison X ≫ (ordinaryCoreCandidate X.op).ι =
      SSet.opFunctor.map (ordinaryCoreCandidate X).ι :=
  SSet.Subcomplex.lift_ι _ _

/-- The inverse comparison also commutes with the original subcomplex inclusions. -/
theorem coreOppositeComparisonInv_comp_ι (X : SSet.{u}) :
    coreOppositeComparisonInv X ≫ SSet.opFunctor.map (ordinaryCoreCandidate X).ι =
      (ordinaryCoreCandidate X.op).ι :=
  liftToOpposite_comp_ι _ _ _

/-- The original core candidate commutes with the actual simplicial opposite by an isomorphism. -/
def coreOppositeIso (X : SSet.{u}) :
    (ordinaryCoreCandidate X : SSet.{u}).op ≅ (ordinaryCoreCandidate X.op : SSet.{u}) where
  hom := coreOppositeComparison X
  inv := coreOppositeComparisonInv X
  hom_inv_id := by
    have : Mono (SSet.opFunctor.map (ordinaryCoreCandidate X).ι) :=
      mono_op_inclusion (ordinaryCoreCandidate X)
    apply (cancel_mono (SSet.opFunctor.map (ordinaryCoreCandidate X).ι)).mp
    rw [Category.assoc, coreOppositeComparisonInv_comp_ι, coreOppositeComparison_comp_ι,
      Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (ordinaryCoreCandidate X.op).ι).mp
    rw [Category.assoc, coreOppositeComparison_comp_ι, coreOppositeComparisonInv_comp_ι,
      Category.id_comp]

end

end DaggerOriginalOrdinaryKanCoreOpposite
