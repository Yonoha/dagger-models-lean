import OriginalJoinedVertexCoreCriterion
import OriginalFullVertexSubcomplexUniversal

/-!
# The original core inside the actual left mapping space

The original core membership of the underlying joined simplex defines a literal
subcomplex of the original strict left mapping space. It is exactly the full
subcomplex on vertices whose original edges are invertible. All suffix vertices
index the initial edges of the same joined simplex; invertibility of those
arrows makes every arrow of the original unit diagram invertible.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership DaggerOriginalOrdinaryKanCoreNerveMembership
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingVertices
open DaggerOriginalJoinedVertexCoreCriterion DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalLeftMappingCoreSubcomplex

noncomputable section

/-- Mapping-space vertices whose same original edge lies in the original ordinary core. -/
def equivalenceVertexSet (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    Set ((leftMappingSpace X x y).obj (op ⦋0⦌)) :=
  {v | edgeIsInvertible X (vertexEdge X x y v).edge}

/-- The literal original-core condition on the underlying original joined simplex. -/
def coreSimplexSubcomplex (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    (leftMappingSpace X x y).Subcomplex where
  obj n := {s | s.val.val ∈ (ordinaryCoreCandidate X).obj
    (op ((ordinalJoinLeft ⦋0⦌).obj n.unop))}
  map φ _ hs :=
    (ordinaryCoreCandidate X).map (((ordinalJoinLeft ⦋0⦌).map φ.unop).op) hs

/-- Membership in the same original core forces every actual mapping-space vertex to be an
 invertible original edge. -/
theorem coreSimplex_vertices {X : SSet.{u}} {x y : X.obj (op ⦋0⦌)}
    (n : SimplexCategoryᵒᵖ) (s : (leftMappingSpace X x y).obj n)
    (hs : s ∈ (coreSimplexSubcomplex X x y).obj n) :
    ∀ φ : ⦋0⦌ ⟶ n.unop, (leftMappingSpace X x y).map φ.op s ∈ equivalenceVertexSet X x y := by
  intro φ
  change edgeIsInvertible X (X.map ((ordinalJoinLeft ⦋0⦌).map φ).op s.val.val)
  exact (mem_ordinaryCoreCandidate_iff_edges_iso X _ s.val.val).mp hs _

/-- Invertibility at all actual mapping-space vertices forces original-core membership of the
 same original simplex. -/
theorem coreSimplex_of_vertices {X : SSet.{u}} {x y : X.obj (op ⦋0⦌)}
    (n : SimplexCategoryᵒᵖ) (s : (leftMappingSpace X x y).obj n)
    (hs : ∀ φ : ⦋0⦌ ⟶ n.unop,
      (leftMappingSpace X x y).map φ.op s ∈ equivalenceVertexSet X x y) :
    s ∈ (coreSimplexSubcomplex X x y).obj n := by
  apply (mem_ordinaryCoreCandidate_iff_unit_arrows_iso X _ s.val.val).mpr
  apply arrows_iso_of_initial_arrows_iso
  intro j
  by_cases hj : j = 0
  · subst j
    have h : homOfLE (Fin.zero_le (0 : Fin
        (((ordinalJoinLeft ⦋0⦌).obj n.unop).len + 1))) = 𝟙 0 := Subsingleton.elim _ _
    rw [h, CategoryTheory.Functor.map_id]
    infer_instance
  · obtain ⟨k, hk⟩ := exists_rightVertex n.unop j hj
    have he := hs ((⦋0⦌ : SimplexCategory).const n.unop k)
    change edgeIsInvertible X (X.map ((ordinalJoinLeft ⦋0⦌).map
      ((⦋0⦌ : SimplexCategory).const n.unop k)).op s.val.val) at he
    rw [joined_vertex_pairOperator, hk] at he
    exact (pair_edge_unit_iso_iff X _ s.val.val 0 j (Fin.zero_le j)).mp he

/-- The actual original-core subcomplex is precisely the full subcomplex on invertible edges. -/
theorem coreSimplexSubcomplex_eq_fullVertexSubcomplex (X : SSet.{u})
    (x y : X.obj (op ⦋0⦌)) :
    coreSimplexSubcomplex X x y =
      fullVertexSubcomplex (leftMappingSpace X x y) (equivalenceVertexSet X x y) := by
  ext n s
  exact ⟨coreSimplex_vertices n s, coreSimplex_of_vertices n s⟩

end

end DaggerOriginalLeftMappingCoreSubcomplex
