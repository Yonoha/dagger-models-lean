import OriginalOrdinaryKanCoreContainsKanSubcomplexes
import Mathlib.AlgebraicTopology.SimplicialSet.Op

/-!
# The actual nerve comparison with simplicial reversal

Use the native equivalence on composable-arrow diagrams to compare the
reversed nerve of a category with the nerve of its opposite. This comparison
is needed for the original homotopy-category unit and the dagger core.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe v u

namespace DaggerOriginalNerveOppositeMap

noncomputable section

/-- Reverse the actual composable-arrow diagram with Mathlib's existing equivalence. -/
def reverseDiagram {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) : ComposableArrows Cᵒᵖ n :=
  (ComposableArrows.opEquivalence C n).functor.obj (op s)

/-- The native reversal is precomposition by finite-order reversal, followed by opposite. -/
theorem reverseDiagram_eq_comp {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) :
    reverseDiagram s = reverseDiagram (n := n) (𝟭 (Fin (n + 1))) ⋙ s.op := rfl

/-- The reversed simplex operator commutes with finite-order reversal before postcomposition. -/
theorem reverseDiagram_whiskerLeft {C : Type u} [Category.{v} C] {m n : SimplexCategory}
    (s : ComposableArrows C n.len) (α : m ⟶ n) :
    reverseDiagram (s.whiskerLeft (SimplexCategory.toCat.map
        (SimplexCategory.rev.map α)).toFunctor) =
      (reverseDiagram s).whiskerLeft (SimplexCategory.toCat.map α).toFunctor := by
  have h : reverseDiagram (n := m.len) (𝟭 (Fin (m.len + 1))) ⋙
        (SimplexCategory.toCat.map (SimplexCategory.rev.map α)).toFunctor.op =
      (SimplexCategory.toCat.map α).toFunctor ⋙
        reverseDiagram (n := n.len) (𝟭 (Fin (n.len + 1))) := by
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun i j f ↦ Subsingleton.elim _ _)
    change op ((SimplexCategory.rev.map α).toOrderHom i.rev) =
      op ((α.toOrderHom i).rev)
    simp only [SimplexCategory.rev_map_apply, Fin.rev_rev]
    rfl
  rw [reverseDiagram_eq_comp (s.whiskerLeft
    (SimplexCategory.toCat.map (SimplexCategory.rev.map α)).toFunctor),
    reverseDiagram_eq_comp s]
  exact congrArg (fun F ↦ F ⋙ s.op) h

/-- A genuine natural comparison from the reversed nerve to the opposite-category nerve. -/
def nerveOppositeMap (C : Type u) [Category.{v} C] :
    (nerve C).op ⟶ nerve Cᵒᵖ where
  app q s := reverseDiagram (SSet.opObjEquiv s)
  naturality n m f := by
    funext s
    change reverseDiagram (SSet.opObjEquiv ((nerve C).op.map f s)) =
      (reverseDiagram (SSet.opObjEquiv s)).whiskerLeft
        (SimplexCategory.toCat.map f.unop).toFunctor
    rw [SSet.op_map]
    change reverseDiagram ((nerve C).map (SimplexCategory.rev.map f.unop).op
      (SSet.opObjEquiv s)) = _
    exact reverseDiagram_whiskerLeft (SSet.opObjEquiv s) f.unop

end

end DaggerOriginalNerveOppositeMap
