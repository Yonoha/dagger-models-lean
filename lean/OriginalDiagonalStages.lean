import BisimplicialDiagonalData
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Subfunctor.Image

/-! D3 source implementation only; no declarations here have been runtime checked.
The stages are subcomplexes of the same accepted diagonal, with all original operators. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerBisimplicialDiagonal

universe u
namespace DaggerOriginalDiagonalStages

/-- Applying an arbitrary diagonal operator keeps the same outer-degree witness. -/
theorem rowImage_operator (B : SimplicialObject SSet.{u})
    {q q' : SimplexCategoryᵒᵖ} (beta : q ⟶ q') (n : ℕ)
    (alpha : q.unop ⟶ ⦋n⦌) (y : (B.obj (op ⦋n⦌)).obj q) :
    (DaggerBisimplicialDiagonal.diag B).map beta ((B.map alpha.op).app q y) =
      (B.map (beta.unop ≫ alpha).op).app q' ((B.obj (op ⦋n⦌)).map beta y) := by
  rw [diag_map_other_order]
  change (B.map beta).app q' ((B.obj q).map beta ((B.map alpha.op).app q y)) = _
  rw [← FunctorToTypes.naturality _ _ (B.map alpha.op) beta y]
  have h := congrFun (NatTrans.congr_app (B.map_comp alpha.op beta) q')
    ((B.obj (op ⦋n⦌)).map beta y)
  change _ = (B.map (alpha.op ≫ beta)).app q' ((B.obj (op ⦋n⦌)).map beta y)
  simpa only [NatTrans.comp_app, types_comp_apply] using h.symm

/-- The literal union of outer-degree images, with degree strictly below r. -/
def stage (B : SimplicialObject SSet.{u}) (r : ℕ) : (DaggerBisimplicialDiagonal.diag B).Subcomplex where
  obj q := {x | ∃ n < r, ∃ alpha : q.unop ⟶ ⦋n⦌,
    ∃ y : (B.obj (op ⦋n⦌)).obj q, (B.map alpha.op).app q y = x}
  map beta := by
    rintro x ⟨n, hn, alpha, y, rfl⟩
    exact ⟨n, hn, beta.unop ≫ alpha, (B.obj (op ⦋n⦌)).map beta y,
      (rowImage_operator B beta n alpha y).symm⟩

theorem mem_stage_iff (B : SimplicialObject SSet.{u}) (r : ℕ)
    (q : SimplexCategoryᵒᵖ) (x : (DaggerBisimplicialDiagonal.diag B).obj q) :
    x ∈ (stage B r).obj q ↔ ∃ n < r, ∃ alpha : q.unop ⟶ ⦋n⦌,
      ∃ y : (B.obj (op ⦋n⦌)).obj q, (B.map alpha.op).app q y = x := Iff.rfl

theorem stage_operator (B : SimplicialObject SSet.{u}) (r : ℕ)
    {q q' : SimplexCategoryᵒᵖ} (beta : q ⟶ q')
    {x : (DaggerBisimplicialDiagonal.diag B).obj q} (hx : x ∈ (stage B r).obj q) :
    (DaggerBisimplicialDiagonal.diag B).map beta x ∈ (stage B r).obj q' := (stage B r).map beta hx

theorem stage_zero (B : SimplicialObject SSet.{u}) : stage B 0 = ⊥ := by
  ext q x
  constructor
  · rintro ⟨n, hn, _, _, _⟩
    exact False.elim ((Nat.not_lt_zero n) hn)
  · intro hx
    exact False.elim hx

theorem stage_monotone (B : SimplicialObject SSet.{u}) {r s : ℕ} (h : r ≤ s) :
    stage B r ≤ stage B s := by
  rintro q x ⟨n, hn, alpha, y, hy⟩
  exact ⟨n, lt_of_lt_of_le hn h, alpha, y, hy⟩

theorem stage_le_succ (B : SimplicialObject SSet.{u}) (r : ℕ) :
    stage B r ≤ stage B (r + 1) := stage_monotone B (Nat.le_succ r)

/-- Every actual degree-q simplex enters at q.len+1 using the identity outer map. -/
theorem simplex_mem_stage (B : SimplicialObject SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (x : (DaggerBisimplicialDiagonal.diag B).obj q) : x ∈ (stage B (q.unop.len + 1)).obj q := by
  refine ⟨q.unop.len, Nat.lt_succ_self _, 𝟙 q.unop, x, ?_⟩
  change (B.map (𝟙 q)).app q x = x
  rw [B.map_id]
  rfl

theorem simplex_appears (B : SimplicialObject SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (x : (DaggerBisimplicialDiagonal.diag B).obj q) : ∃ r, ∃ y : (stage B r).obj q, y.val = x :=
  ⟨q.unop.len + 1, ⟨x, simplex_mem_stage B q x⟩, rfl⟩

theorem stage_exhaustive (B : SimplicialObject SSet.{u}) : (⨆ r, stage B r) = ⊤ := by
  ext q x
  simp only [Subfunctor.iSup_obj, Subfunctor.top_obj, Set.mem_iUnion]
  refine iff_of_true ?_ (by trivial)
  exact ⟨q.unop.len + 1, simplex_mem_stage B q x⟩

def stageZeroIso (B : SimplicialObject SSet.{u}) :
    (stage B 0 : SSet.{u}) ≅ (⊥ : (DaggerBisimplicialDiagonal.diag B).Subcomplex) :=
  SSet.Subcomplex.eqToIso (stage_zero B)

/-- Eta may create degeneracies; the same alpha and degree still give a stage witness. -/
theorem stageMap_preserves {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (r : ℕ)
    (q : SimplexCategoryᵒᵖ) {x : (DaggerBisimplicialDiagonal.diag B).obj q} (hx : x ∈ (stage B r).obj q) :
    (diagMap eta).app q x ∈ (stage B' r).obj q := by
  obtain ⟨n, hn, alpha, y, hy⟩ := hx
  refine ⟨n, hn, alpha, (eta.app (op ⦋n⦌)).app q y, ?_⟩
  have h := congrFun (NatTrans.congr_app (eta.naturality alpha.op) q) y
  change (eta.app q).app q ((B.map alpha.op).app q y) =
    (B'.map alpha.op).app q ((eta.app (op ⦋n⦌)).app q y) at h
  exact h.symm.trans (congrArg ((diagMap eta).app q) hy)

/-- Existing subfunctor lifting restricts the SAME diagonal comparison. -/
def stageMap {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (r : ℕ) :
    (stage B r : SSet.{u}) ⟶ (stage B' r : SSet.{u}) :=
  Subfunctor.lift ((stage B r).ι ≫ diagMap eta) (by
    rintro q z ⟨x, rfl⟩
    exact stageMap_preserves eta r q x.property)

@[simp] theorem stageMap_app_val {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    (r : ℕ) (q : SimplexCategoryᵒᵖ) (x : (stage B r).obj q) :
    ((stageMap eta r).app q x).val = (diagMap eta).app q x.val := rfl

@[reassoc] theorem stageMap_ι {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (r : ℕ) :
    stageMap eta r ≫ (stage B' r).ι = (stage B r).ι ≫ diagMap eta := rfl

theorem stageMap_naturality {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B')
    {r s : ℕ} (h : r ≤ s) :
    SSet.Subcomplex.homOfLE (stage_monotone B h) ≫ stageMap eta s =
      stageMap eta r ≫ SSet.Subcomplex.homOfLE (stage_monotone B' h) := by
  ext q x
  rfl

@[simp] theorem stageMap_id (B : SimplicialObject SSet.{u}) (r : ℕ) :
    stageMap (𝟙 B) r = 𝟙 (stage B r : SSet.{u}) := by
  ext q x
  rfl

@[simp] theorem stageMap_comp {B B' B'' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (theta : B' ⟶ B'') (r : ℕ) :
    stageMap (eta ≫ theta) r = stageMap eta r ≫ stageMap theta r := by
  ext q x
  rfl

end DaggerOriginalDiagonalStages
