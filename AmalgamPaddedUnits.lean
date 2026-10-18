import AmalgamNormalPaths
import AmalgamNormalForms
import Mathlib.Data.Fin.Tuple.Basic

/-! The full original critical unit predicates and actual singleton normalization.
Endpoint C padding is not a critical coordinate. No full SSet family is redeclared. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u

namespace DaggerAmalgamPaddedClassifier

noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def criticalOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) :
    (r : ℕ) → RawOO C B x b q a d r → Prop
  | 0, _ => False
  | _ + 1, h =>
      (∃ i, h.2.1 i = (eId SSet b).app q PUnit.unit) ∨
        ∃ i, h.2.2.1 i = (eId SSet x).app q PUnit.unit

def criticalON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) : Prop :=
  (∃ i, h.2.1 i = (eId SSet b).app q PUnit.unit) ∨
    ∃ i, h.2.2.1 i = (eId SSet x).app q PUnit.unit

def criticalNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) : Prop :=
  (∃ i, h.2.1 i = (eId SSet x).app q PUnit.unit) ∨
    ∃ i, h.2.2.1 i = (eId SSet b).app q PUnit.unit

def criticalNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) :
    (r : ℕ) → RawNN C B x b q z w r → Prop
  | 0, _ => False
  | _ + 1, h =>
      (∃ i, h.2.1 i = (eId SSet x).app q PUnit.unit) ∨
        ∃ i, h.2.2.1 i = (eId SSet b).app q PUnit.unit

abbrev InteriorOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ) :=
  {h : RawOO C B x b q a d r // ¬ criticalOO C B x b q a d r h}
abbrev InteriorON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ) :=
  {h : RawON C B x b q a w r // ¬ criticalON C B x b q a w r h}
abbrev InteriorNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ) :=
  {h : RawNO C B x b q z d r // ¬ criticalNO C B x b q z d r h}
abbrev InteriorNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ) :=
  {h : RawNN C B x b q z w r // ¬ criticalNN C B x b q z w r h}

theorem criticalNN_one (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (h : RawNN C B x b q z w 1) :
    criticalNN C B x b q z w 1 h ↔ h.2.1 0 = (eId SSet x).app q PUnit.unit := by
  simp [criticalNN, Fin.exists_fin_one]

/-- A tagged identity retains its full original source and target. -/
theorem identity_endpoints {q : SimplexCategoryᵒᵖ} {e : Edge C B q}
    (he : IsIdentity C B q e) : source C B x b e = target C B x b e := by
  cases he
  rfl

/-- The original normalization of a singleton removes exactly original identity letters. -/
def trimmedTag (q : SimplexCategoryᵒᵖ) (c : Bool)
    {a d : At C B q c} (h : a ⟶ d) : List (Edge C B q) := by
  classical
  exact if IsIdentity C B q (tag C B q c h) then [] else [tag C B q c h]

theorem normalize_factor_encode (q : SimplexCategoryᵒᵖ) (c : Bool)
    {a d : At C B q c} (h : a ⟶ d) :
    encode C B x b (DaggerAmalgamNormalForms.normalize C B x b
      (factorPath C B x b c q h)).val =
        trimmedTag C B q c h := by
  classical
  unfold trimmedTag
  by_cases hi : IsIdentity C B q (tag C B q c h)
  · cases hi
    rw [if_pos (IsIdentity.intro _ _)]
    have hr := @HomRel.CompClosure.of
      (SimplicialEnrichment.At (free C B x b).Obj q) _
      (SimplicialCat.HomQuotient.degreeRel (relations C B x b) q) _ _ _ _
      (@Rel.factorId C B x b q c a)
    have hn := DaggerAmalgamNormalForms.normalize_finite C B x b
      (Relation.ReflTransGen.single hr)
    change DaggerAmalgamNormalForms.normalize C B x b
      (factorPath C B x b c q (𝟙 a)) =
        DaggerAmalgamNormalForms.normalize C B x b .nil at hn
    rw [hn]
    rw [DaggerAmalgamNormalForms.normalize_of_normal C B x b
      ⟨.nil, normal_nil C B x b q _⟩]
    rfl
  · rw [if_neg hi]
    have hn := DaggerAmalgamNormalForms.normalize_of_normal C B x b
      ⟨factorPath C B x b c q h, (normal_factorPath_iff C B x b c h).2 hi⟩
    rw [hn]
    rfl

end
end DaggerAmalgamPaddedClassifier
