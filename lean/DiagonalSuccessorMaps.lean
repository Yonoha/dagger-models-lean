import DiagonalSuccessorMembership

/-! Exact D5 maps, all operators and the entire eta comparison cube; source only. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerBisimplicialDiagonal DaggerOriginalDiagonalStages

universe u
namespace DaggerOriginalDiagonalSuccessor
noncomputable section

/-- Restrict the same row evaluation to the actual next stage. -/
def rowEvalStage (B : SimplicialObject SSet.{u}) (n : ℕ) :
    B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ (stage B (n + 1) : SSet.{u}) :=
  Subfunctor.lift (rowEval B n) (by
    rintro q x ⟨p, rfl⟩
    exact rowEval_mem_succ B n q p)

/-- Restrict the same evaluation on the whole attaching union to the old stage. -/
def attachingToStage (B : SimplicialObject SSet.{u}) (n : ℕ) :
    (attaching B n : SSet.{u}) ⟶ (stage B n : SSet.{u}) :=
  Subfunctor.lift ((attaching B n).ι ≫ rowEval B n) (by
    rintro q x ⟨p, rfl⟩
    exact (rowEval_preimage B n q p.val).2 p.property)

/-- This is the original D3 inclusion, not an isomorphic replacement. -/
abbrev transition (B : SimplicialObject SSet.{u}) (n : ℕ) :
    (stage B n : SSet.{u}) ⟶ (stage B (n + 1) : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (stage_le_succ B n)

@[simp] theorem rowEvalStage_app_val (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ)
    (p : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q) :
    ((rowEvalStage B n).app q p).val = (rowEval B n).app q p := rfl

@[simp] theorem attachingToStage_app_val (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (p : (attaching B n).obj q) :
    ((attachingToStage B n).app q p).val = (rowEval B n).app q p.val := rfl

@[reassoc] theorem rowEvalStage_ι (B : SimplicialObject SSet.{u}) (n : ℕ) :
    rowEvalStage B n ≫ (stage B (n + 1)).ι = rowEval B n := rfl

@[reassoc] theorem attachingToStage_ι (B : SimplicialObject SSet.{u}) (n : ℕ) :
    attachingToStage B n ≫ (stage B n).ι = (attaching B n).ι ≫ rowEval B n := rfl

theorem successor_w (B : SimplicialObject SSet.{u}) (n : ℕ) :
    (attaching B n).ι ≫ rowEvalStage B n = attachingToStage B n ≫ transition B n := by
  ext q p
  rfl

theorem rowEvalStage_operator (B : SimplicialObject SSet.{u}) (n : ℕ)
    {q q' : SimplexCategoryᵒᵖ} (beta : q ⟶ q') :
    (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).map beta ≫ (rowEvalStage B n).app q' =
      (rowEvalStage B n).app q ≫ (stage B (n + 1) : SSet.{u}).map beta :=
  (rowEvalStage B n).naturality beta

theorem attachingToStage_operator (B : SimplicialObject SSet.{u}) (n : ℕ)
    {q q' : SimplexCategoryᵒᵖ} (beta : q ⟶ q') :
    (attaching B n : SSet.{u}).map beta ≫ (attachingToStage B n).app q' =
      (attachingToStage B n).app q ≫ (stage B n : SSet.{u}).map beta :=
  (attachingToStage B n).naturality beta

theorem rowEvalStage_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (n : ℕ) :
    rowEvalStage B n ≫ stageMap eta (n + 1) =
      (eta.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) ≫ rowEvalStage B' n := by
  ext q p
  exact congrFun (NatTrans.congr_app (rowEval_naturality eta n) q) p

theorem attachingToStage_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (n : ℕ) :
    attachingToStage B n ≫ stageMap eta n = attachingMap eta n ≫ attachingToStage B' n := by
  ext q p
  exact congrFun (NatTrans.congr_app (rowEval_naturality eta n) q) p.val

theorem transition_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (n : ℕ) :
    transition B n ≫ stageMap eta (n + 1) = stageMap eta n ≫ transition B' n :=
  stageMap_naturality eta (Nat.le_succ n)

/-- Every successor element is in the literal range of one of the two output legs. -/
theorem successor_coverage (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (x : (stage B (n + 1)).obj q) :
    (∃ y : (stage B n).obj q, (transition B n).app q y = x) ∨
      ∃ p : (B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q,
        (rowEvalStage B n).app q p = x := by
  obtain hx | ⟨p, hp⟩ := (mem_stage_succ_iff B n q x.val).1 x.property
  · exact Or.inl ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
  · exact Or.inr ⟨p, Subtype.ext hp⟩

end
end DaggerOriginalDiagonalSuccessor
