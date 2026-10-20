import DiagonalSuccessorMaps
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! D5 source-only exact successor pushout, with its full arbitrary-target UP. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerBisimplicialDiagonal DaggerOriginalDiagonalStages

universe u
namespace DaggerOriginalDiagonalSuccessor
noncomputable section

/-- Exact pullback of the old-stage inclusion along the SAME row evaluation. -/
theorem successorDegreePullback (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) :
    IsPullback ((attachingToStage B n).app q) ((attaching B n).ι.app q)
      ((transition B n).app q) ((rowEvalStage B n).app q) := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨NatTrans.congr_app (successor_w B n).symm q, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext h.2
  · intro x p h
    have hv : x.val = (rowEval B n).app q p := congrArg Subtype.val h
    have hx : (rowEval B n).app q p ∈ (stage B n).obj q := by
      rw [← hv]
      exact x.property
    refine ⟨⟨p, (rowEval_preimage B n q p).1 hx⟩, Subtype.ext hv.symm, rfl⟩

/-- Joint surjectivity is literal coverage by the original two ranges. -/
theorem successorDegreeRanges (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) :
    Set.range ((transition B n).app q) ⊔ Set.range ((rowEvalStage B n).app q) = Set.univ := by
  ext x
  simp only [Set.sup_eq_union, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  exact successor_coverage B n q x

/-- The Types criterion uses the complement of the WHOLE attaching inclusion range. -/
theorem successorDegreeLowerFirst (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) :
    IsPushout ((attachingToStage B n).app q) ((attaching B n).ι.app q)
      ((transition B n).app q) ((rowEvalStage B n).app q) := by
  letI : Mono ((transition B n).app q) :=
    (mono_iff_injective _).2 (fun x y h ↦
      Subtype.ext (congrArg (fun z : (stage B (n + 1)).obj q ↦ z.val) h))
  apply Types.isPushout_of_isPullback_of_mono' (successorDegreePullback B n q)
    (successorDegreeRanges B n q)
  intro p p' hp hp' h
  apply rowEval_interior_injective B n q p p'
  · intro hmem
    exact hp ⟨⟨p, hmem⟩, rfl⟩
  · intro hmem
    exact hp' ⟨⟨p', hmem⟩, rfl⟩
  · exact congrArg Subtype.val h

/-- The exported square is cell first and old stage second. -/
theorem successorDegreeIsPushout (B : SimplicialObject SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) :
    IsPushout ((attaching B n).ι.app q) ((attachingToStage B n).app q)
      ((rowEvalStage B n).app q) ((transition B n).app q) :=
  (successorDegreeLowerFirst B n q).flip

/-- Existing evaluation reflection gives the entire simplicial pushout UP. -/
theorem successorIsPushout (B : SimplicialObject SSet.{u}) (n : ℕ) :
    IsPushout (attaching B n).ι (attachingToStage B n) (rowEvalStage B n) (transition B n) where
  w := successor_w B n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun q ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2
      (successorDegreeIsPushout B n q).isColimit)⟩

/-- The full record, with the SAME supplied cell-first cocone. -/
def successorIsColimit (B : SimplicialObject SSet.{u}) (n : ℕ) :
    IsColimit (PushoutCocone.mk (rowEvalStage B n) (transition B n) (successor_w B n)) :=
  (successorIsPushout B n).isColimit

def successorDesc (B : SimplicialObject SSet.{u}) (n : ℕ) {Z : SSet.{u}}
    (cell : B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B n : SSet.{u}) ⟶ Z)
    (h : (attaching B n).ι ≫ cell = attachingToStage B n ≫ old) :
    (stage B (n + 1) : SSet.{u}) ⟶ Z :=
  (successorIsPushout B n).desc cell old h

@[reassoc] theorem successorDesc_cell (B : SimplicialObject SSet.{u}) (n : ℕ)
    {Z : SSet.{u}} (cell : B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B n : SSet.{u}) ⟶ Z)
    (h : (attaching B n).ι ≫ cell = attachingToStage B n ≫ old) :
    rowEvalStage B n ≫ successorDesc B n cell old h = cell :=
  (successorIsPushout B n).inl_desc cell old h

@[reassoc] theorem successorDesc_old (B : SimplicialObject SSet.{u}) (n : ℕ)
    {Z : SSet.{u}} (cell : B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B n : SSet.{u}) ⟶ Z)
    (h : (attaching B n).ι ≫ cell = attachingToStage B n ≫ old) :
    transition B n ≫ successorDesc B n cell old h = old :=
  (successorIsPushout B n).inr_desc cell old h

theorem successorDesc_unique (B : SimplicialObject SSet.{u}) (n : ℕ)
    {Z : SSet.{u}} (cell : B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B n : SSet.{u}) ⟶ Z)
    (h : (attaching B n).ι ≫ cell = attachingToStage B n ≫ old)
    (m : (stage B (n + 1) : SSet.{u}) ⟶ Z)
    (hc : rowEvalStage B n ≫ m = cell) (ho : transition B n ≫ m = old) :
    m = successorDesc B n cell old h :=
  (successorIsPushout B n).hom_ext (hc.trans (successorDesc_cell B n cell old h).symm)
    (ho.trans (successorDesc_old B n cell old h).symm)

theorem successorDesc_operator (B : SimplicialObject SSet.{u}) (n : ℕ)
    {Z : SSet.{u}} (cell : B.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B n : SSet.{u}) ⟶ Z)
    (h : (attaching B n).ι ≫ cell = attachingToStage B n ≫ old)
    {q q' : SimplexCategoryᵒᵖ} (beta : q ⟶ q') :
    (stage B (n + 1) : SSet.{u}).map beta ≫ (successorDesc B n cell old h).app q' =
      (successorDesc B n cell old h).app q ≫ Z.map beta :=
  (successorDesc B n cell old h).naturality beta

/-- Eta induces the SAME arbitrary-target cocone, without reflecting any degeneracy. -/
theorem comparison_cocone_w {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (n : ℕ) {Z : SSet.{u}}
    (cell : B'.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B' n : SSet.{u}) ⟶ Z)
    (h : (attaching B' n).ι ≫ cell = attachingToStage B' n ≫ old) :
    (attaching B n).ι ≫ (eta.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) ≫ cell =
      attachingToStage B n ≫ stageMap eta n ≫ old := by
  rw [← Category.assoc, attachingMap_ι, Category.assoc, h,
    ← Category.assoc, ← attachingToStage_naturality, Category.assoc]

theorem successorDesc_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (n : ℕ) {Z : SSet.{u}}
    (cell : B'.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ Z)
    (old : (stage B' n : SSet.{u}) ⟶ Z)
    (h : (attaching B' n).ι ≫ cell = attachingToStage B' n ≫ old) :
    stageMap eta (n + 1) ≫ successorDesc B' n cell old h =
      successorDesc B n ((eta.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) ≫ cell)
        (stageMap eta n ≫ old) (comparison_cocone_w eta n cell old h) := by
  apply successorDesc_unique
  · rw [← Category.assoc, rowEvalStage_naturality, Category.assoc, successorDesc_cell]
  · rw [← Category.assoc, transition_naturality, Category.assoc, successorDesc_old]

end
end DaggerOriginalDiagonalSuccessor
