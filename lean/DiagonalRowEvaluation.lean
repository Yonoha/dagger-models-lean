import BisimplicialDiagonalData
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! D4 source candidate: the literal row evaluation, with every inner operator.
No stage, successor pushout or geometric weak-equivalence theorem is asserted here. -/

open CategoryTheory Opposite Simplicial MonoidalCategory

universe u

namespace DaggerBisimplicialDiagonal

/-- Evaluate the outer simplex operator on the given row element. -/
def rowEval (B : SimplicialObject SSet.{u}) (n : ℕ) :
    B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ diag B where
  app q x := (B.map (SSet.stdSimplex.objEquiv x.2).op).app q x.1
  naturality := by
    intro q r beta
    rw [diag_map_other_order]
    funext x
    change (B.map ((SSet.stdSimplex.objEquiv x.2).op ≫ beta)).app r
        ((B.obj (op ⦋n⦌)).map beta x.1) =
      (B.map beta).app r
        ((B.obj q).map beta
          ((B.map (SSet.stdSimplex.objEquiv x.2).op).app q x.1))
    rw [B.map_comp]
    exact congrArg ((B.map beta).app r)
      (congr_fun ((B.map (SSet.stdSimplex.objEquiv x.2).op).naturality beta) x.1)

theorem rowEval_app (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (x : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q) :
    (rowEval B n).app q x =
      (B.map (SSet.stdSimplex.objEquiv x.2).op).app q x.1 := rfl

theorem rowEval_operator (B : SimplicialObject SSet.{u}) (n : ℕ)
    {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).map beta ≫ (rowEval B n).app r =
      (rowEval B n).app q ≫ (diag B).map beta :=
  (rowEval B n).naturality beta

theorem rowEval_naturality {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) :
    rowEval B n ≫ diagMap eta =
      (eta.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) ≫ rowEval B' n := by
  ext q x
  exact congr_fun
    (congr_app (eta.naturality (SSet.stdSimplex.objEquiv x.2).op) q) x.1

end DaggerBisimplicialDiagonal
