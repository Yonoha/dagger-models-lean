import DiagonalRowEvaluation
import LatchingOriginalData
import TopCatModelCategory.SSet.Subcomplex

/-! D4 source candidate: the whole original attaching union and its eta map.
No preimage equality, interior injection or successor pushout is assumed. -/

open CategoryTheory Opposite Simplicial MonoidalCategory

universe u

namespace DaggerBisimplicialDiagonal

/-- The original latching-times-simplex union row-times-boundary. -/
noncomputable def attaching (B : SimplicialObject SSet.{u}) (n : ℕ) :
    (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).Subcomplex :=
  (latching B n).unionProd (SSet.boundary n)

theorem attaching_mem_iff (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (x : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q) :
    x ∈ (attaching B n).obj q ↔
      x.1 ∈ (latching B n).obj q ∨
        ¬Function.Surjective (SSet.stdSimplex.asOrderHom x.2) :=
  SSet.Subcomplex.mem_unionProd_iff (latching B n) (SSet.boundary n) x

theorem attaching_zero (B : SimplicialObject SSet.{u}) :
    attaching B 0 = ⊥ := by
  ext q x
  change x ∈ ((latching B 0).unionProd (SSet.boundary 0)).obj q ↔
    x ∈ (⊥ : (B.obj (op ⦋0⦌) ⊗ (Δ[0] : SSet.{u})).Subcomplex).obj q
  rw [SSet.Subcomplex.mem_unionProd_iff, latching_zero, SSet.boundary_zero]
  simp

/-- Restriction of the same row comparison times the identity simplex map. -/
noncomputable def attachingMap {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) :
    (attaching B n : SSet.{u}) ⟶ (attaching B' n : SSet.{u}) :=
  SSet.Subcomplex.lift
    ((attaching B n).ι ≫ (eta.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u}))) (by
      rintro q x ⟨z, rfl⟩
      apply (attaching_mem_iff B' n q _).2
      obtain hz | hz := (attaching_mem_iff B n q z.val).1 z.property
      · exact Or.inl (((latchingMap eta n).app q ⟨z.val.1, hz⟩).property)
      · exact Or.inr hz)

theorem attachingMap_app {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (attaching B n).obj q) :
    ((attachingMap eta n).app q x).val =
      ((eta.app (op ⦋n⦌)).app q x.val.1, x.val.2) := rfl

theorem attachingMap_ι {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) :
    (attaching B n).ι ≫ (eta.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) =
      attachingMap eta n ≫ (attaching B' n).ι :=
  (SSet.Subcomplex.lift_ι _ _).symm

theorem attachingMap_operator {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (attaching B n : SSet.{u}).map beta ≫ (attachingMap eta n).app r =
      (attachingMap eta n).app q ≫ (attaching B' n : SSet.{u}).map beta :=
  (attachingMap eta n).naturality beta

theorem attachingMap_rowEval {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) :
    (attaching B n).ι ≫ rowEval B n ≫ diagMap eta =
      attachingMap eta n ≫ (attaching B' n).ι ≫ rowEval B' n := by
  rw [rowEval_naturality, ← Category.assoc, attachingMap_ι, Category.assoc]

end DaggerBisimplicialDiagonal
