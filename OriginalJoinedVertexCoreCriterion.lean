import OriginalLeftMappingFunctoriality
import OriginalOrdinaryCoreKan

/-!
# Initial-edge criterion for the original joined simplex to lie in the core

The native ordinal join of a vertex with an ordinal has initial edges indexed
by its suffix vertices. In a composable-arrow diagram, invertibility of every
arrow from the initial vertex implies invertibility of every arrow. Naturality
of the original homotopy-category unit identifies these arrows with the exact
original simplicial edge predicate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreEdgeMembership

universe v u

namespace DaggerOriginalJoinedVertexCoreCriterion

noncomputable section

/-- Every arrow of a diagram is invertible if all arrows from its initial vertex are invertible.
-/
theorem arrows_iso_of_initial_arrows_iso {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n)
    (hs : ∀ j : Fin (n + 1), IsIso (s.map (homOfLE (Fin.zero_le j)))) :
    ∀ {i j : Fin (n + 1)} (f : i ⟶ j), IsIso (s.map f) := by
  intro i j f
  haveI := hs i
  haveI := hs j
  apply (isIso_comp_left_iff (s.map (homOfLE (Fin.zero_le i))) (s.map f)).mp
  rw [← s.map_comp]
  have h : homOfLE (Fin.zero_le i) ≫ f = homOfLE (Fin.zero_le j) := Subsingleton.elim _ _
  rw [h]
  infer_instance

/-- The actual right vertex in the native joined ordinal, with its native length convention. -/
def rightVertex (n : SimplexCategory) (j : Fin (n.len + 1)) :
    Fin ((AugmentedSimplexCategory.tensorObjOf ⦋0⦌ n).len + 1) :=
  ⟨j.val + 1, by dsimp [AugmentedSimplexCategory.tensorObjOf]; omega⟩

/-- Joining the initial vertex to a suffix vertex selects the exact original initial edge. -/
theorem joined_vertex_pairOperator (n : SimplexCategory) (j : Fin (n.len + 1)) :
    (ordinalJoinLeft ⦋0⦌).map ((⦋0⦌ : SimplexCategory).const n j) =
      pairOperator (0 : Fin ((AugmentedSimplexCategory.tensorObjOf ⦋0⦌ n).len + 1))
        (rightVertex n j) (Fin.zero_le _) := by
  ext i
  fin_cases i <;> simp [ordinalJoinLeft, AugmentedSimplexCategory.tensorHomOf,
    pairOperator, SimplexCategory.const, SimplexCategory.eqToHom_toOrderHom, OrderHom.coe_mk,
    rightVertex]
  all_goals first | rfl | (change 1 + j.val = j.val + 1; omega)

/-- Every noninitial joined vertex is exactly one of the original suffix vertices. -/
theorem exists_rightVertex (n : SimplexCategory)
    (j : Fin ((AugmentedSimplexCategory.tensorObjOf ⦋0⦌ n).len + 1)) (hj : j ≠ 0) :
    ∃ k : Fin (n.len + 1), rightVertex n k = j := by
  have hpos : 0 < j.val := by
    have hne : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
    omega
  let k : Fin (n.len + 1) := ⟨j.val - 1, by
    have hb := j.isLt
    dsimp [AugmentedSimplexCategory.tensorObjOf] at hb
    omega⟩
  refine ⟨k, ?_⟩
  apply Fin.ext
  change (j.val - 1) + 1 = j.val
  omega

/-- A selected original edge is invertible exactly when the same arrow of the unit diagram is.
-/
theorem pair_edge_unit_iso_iff (X : SSet.{u}) (n : ℕ) (s : X.obj (op ⦋n⦌))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    edgeIsInvertible X (X.map (pairOperator i j hij).op s) ↔
      IsIso (((homotopyCategoryUnit X).app (op ⦋n⦌) s).map (homOfLE hij)) := by
  have hn := congrFun ((homotopyCategoryUnit X).naturality (pairOperator i j hij).op) s
  change (homotopyCategoryUnit X).app (op ⦋1⦌) (X.map (pairOperator i j hij).op s) =
    (nerve (SSet.hoFunctor.obj X)).map (pairOperator i j hij).op
      ((homotopyCategoryUnit X).app (op ⦋n⦌) s) at hn
  dsimp [edgeIsInvertible]
  rw [hn, pairOperator_nerve_hom]

end

end DaggerOriginalJoinedVertexCoreCriterion
