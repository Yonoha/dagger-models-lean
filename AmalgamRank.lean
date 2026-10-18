import AmalgamNormalComposition
import AmalgamPathMeasure
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-! Actual count and predecessor-count subcomplexes in the SAME original quotient Hom.
No irreducibility preservation or weak-equivalence claim is assumed. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPathMeasure DaggerAmalgamNormalForms

universe u

namespace DaggerAmalgamRankFiltration

noncomputable section

variable (C B : SimplicialCat.{u, u}) (c : C.Obj) (b : B.Obj)

/-- The original count of B letters in the actual normal representative. -/
def rank (q : SimplexCategoryᵒᵖ) {a z : Objects C B c b}
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) : ℕ :=
  rightCount C B c b q (homEquiv C B c b q a z h).val

def predRank (q : SimplexCategoryᵒᵖ) {a z : Objects C B c b}
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) : ℕ :=
  (rank C B c b q h).pred

/-- False gives the OO count convention; true gives the ON/NO/NN predecessor convention. -/
def rankOf (shift : Bool) (q : SimplexCategoryᵒᵖ) {a z : Objects C B c b}
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) : ℕ :=
  if shift then predRank C B c b q h else rank C B c b q h

/-- Renormalization, not preservation of normal words, proves the operator bound. -/
theorem rank_map_le {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects C B c b}
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    rank C B c b q' (SimplicialCat.HomQuotient.map _ α h) ≤ rank C B c b q h := by
  unfold rank
  rw [normalize_map]
  have ht := rightCount_reflTransGen_le C B c b
    (normalForm_reduces C B c b
      (SimplicialColimitsFree.Paths.map (graph C B c b) α (homEquiv C B c b q a z h).val))
  exact ht.trans_eq (rightCount_map C B c b α _)

theorem predRank_map_le {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects C B c b}
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    predRank C B c b q' (SimplicialCat.HomQuotient.map _ α h) ≤ predRank C B c b q h :=
  Nat.pred_le_pred (rank_map_le C B c b α h)

theorem rankOf_map_le (shift : Bool) {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects C B c b}
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    rankOf C B c b shift q' (SimplicialCat.HomQuotient.map _ α h) ≤
      rankOf C B c b shift q h := by
  cases shift
  · exact rank_map_le C B c b α h
  · exact predRank_map_le C B c b α h

/-- Literal bounded-rank subcomplex of the original quotient Hom. -/
def stage (shift : Bool) (n : ℕ) (a z : Objects C B c b) :
    (SimplicialCat.HomQuotient.hom (relations C B c b) a z).Subcomplex where
  obj q := {h | rankOf C B c b shift q h ≤ n}
  map α h hh := (rankOf_map_le C B c b shift α h).trans hh

@[simp] theorem mem_stage (shift : Bool) (n : ℕ) (a z : Objects C B c b)
    (q : SimplexCategoryᵒᵖ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B c b) q a z) :
    h ∈ (stage C B c b shift n a z).obj q ↔ rankOf C B c b shift q h ≤ n := Iff.rfl

theorem stage_monotone (shift : Bool) (a z : Objects C B c b) :
    Monotone (fun n ↦ stage C B c b shift n a z) := fun _ _ hn _ _ hh ↦ hh.trans hn

/-- Old-to-old endpoints use the exact unshifted count. -/
abbrev oldOldStage (n : ℕ) (a z : C.Obj) :=
  stage C B c b false n (leftObj C B c b a) (leftObj C B c b z)

/-- The other three endpoint families use the same actual predecessor-count subcomplex. -/
abbrev oldNewStage (n : ℕ) (a : C.Obj) (z : B.Obj) :=
  stage C B c b true n (leftObj C B c b a) (rightObj C B c b z)
abbrev newOldStage (n : ℕ) (a : B.Obj) (z : C.Obj) :=
  stage C B c b true n (rightObj C B c b a) (leftObj C B c b z)
abbrev newNewStage (n : ℕ) (a z : B.Obj) :=
  stage C B c b true n (rightObj C B c b a) (rightObj C B c b z)

end
end DaggerAmalgamRankFiltration
