import ActualQuasicategoryMappingFibres
import NativeZeroJoinEdgeClassification
import OriginalFullVertexSubcomplexUniversal

/-! Original mapping-fibre core membership is exactly selection of equivalence vertices. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalOrdinalJoinLeft
open DaggerActualQuasicategoryMappingFibres
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalOrdinaryKanCoreEdgeMaximality DaggerNativeKanSourceOriginalCoreFactor
open DaggerOriginalFullVertexSubcomplex
universe u
namespace DaggerActualMappingCoreVertexCharacterization
noncomputable section

theorem suffix_eq_const (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (q : SimplexCategoryᵒᵖ) (s : (leftMapping X a b).obj q) :
    X.map (AugmentedSimplexCategory.inr' ⦋0⦌ q.unop).op s.val.val =
      (SSet.const b : leftMapping X a b ⟶ X).app q s := by
  have h : (SSet.Subcomplex.fiber (cosliceProjection ⦋0⦌ X a) b).ι ≫
      cosliceProjection ⦋0⦌ X a = (SSet.const b : leftMapping X a b ⟶ X) := by
    exact (SSet.Subcomplex.fiber_isPullback (cosliceProjection ⦋0⦌ X a) b).w.trans
      (by simp only [SSet.yonedaEquiv_symm_zero, SSet.comp_const])
  exact congrFun (NatTrans.congr_app h q) s

def equivalenceVertices (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    Set ((leftMapping X a b).obj (op ⦋0⦌)) :=
  setOf (fun s ↦ edgeIsInvertible X s.val.val)

def corePart (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : (leftMapping X a b).Subcomplex where
  obj q := setOf (fun s ↦ s.val.val ∈
    (ordinaryCoreCandidate X).obj (op ((ordinalJoinLeft ⦋0⦌).obj q.unop)))
  map {_ _} α _ hs :=
    (ordinaryCoreCandidate X).map ((ordinalJoinLeft ⦋0⦌).map α.unop).op hs

theorem raw_mem_core_iff_vertices (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) (n : ℕ) (s : (leftMapping X a b).obj (op ⦋n⦌)) :
    s.val.val ∈ (ordinaryCoreCandidate X).obj (op ((ordinalJoinLeft ⦋0⦌).obj ⦋n⦌)) ↔
      ∀ β : ⦋0⦌ ⟶ ⦋n⦌,
        (leftMapping X a b).map β.op s ∈ equivalenceVertices X a b := by
  constructor
  · intro hs β
    apply (mem_ordinaryCoreCandidate_one_iff X _).1
    exact (ordinaryCoreCandidate X).map ((ordinalJoinLeft ⦋0⦌).map β).op hs
  · intro h
    apply (mem_ordinaryCoreCandidate_iff_edges_iso X _ s.val.val).2
    intro α
    rcases DaggerNativeZeroJoinEdgeClassification.edge_cases n α with hα | ⟨β, hα⟩ | ⟨β, hα⟩
    · subst α
      change edgeIsInvertible X (X.map
        ((AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌).op ≫
          (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) s.val.val)
      rw [X.map_comp]
      change edgeIsInvertible X (X.map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
        (X.map (AugmentedSimplexCategory.inl' ⦋0⦌ ⦋n⦌).op s.val.val))
      rw [s.val.property]
      exact (mem_ordinaryCoreCandidate_one_iff X _).1
        ((ordinaryCoreCandidate X).map (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op
          (vertex_mem_ordinaryCoreCandidate X a))
    · subst α
      exact h β
    · subst α
      have : (leftMapping X a b).KanComplex := leftMapping_kan X a b
      have hs : X.map (AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌).op s.val.val ∈
          (ordinaryCoreCandidate X).obj (op ⦋n⦌) := by
        rw [suffix_eq_const]
        exact kan_map_mem_core (SSet.const b : leftMapping X a b ⟶ X) _ s
      change edgeIsInvertible X (X.map
        ((AugmentedSimplexCategory.inr' ⦋0⦌ ⦋n⦌).op ≫ β.op) s.val.val)
      rw [X.map_comp]
      exact (mem_ordinaryCoreCandidate_one_iff X _).1
        ((ordinaryCoreCandidate X).map β.op hs)

theorem corePart_eq_fullVertex (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) : corePart X a b =
      fullVertexSubcomplex (leftMapping X a b) (equivalenceVertices X a b) := by
  ext q s
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h n =>
      change s.val.val ∈
        (ordinaryCoreCandidate X).obj (op ((ordinalJoinLeft ⦋0⦌).obj ⦋n⦌)) ↔
          ∀ β : ⦋0⦌ ⟶ ⦋n⦌,
            (leftMapping X a b).map β.op s ∈ equivalenceVertices X a b
      exact raw_mem_core_iff_vertices X a b n s

end
end DaggerActualMappingCoreVertexCharacterization
