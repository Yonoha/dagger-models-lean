import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Defs

/-! A generic quotient-normal representative bridge using the existing
Church–Rosser theorem. No two-color reduction or stage theorem is assumed. -/

set_option autoImplicit false
open Relation
universe u v

namespace DaggerNormalFormQuotient

def Normal {α : Type u} (r : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ r a b

/-- The exact asymmetric one-step/finite-step premise of `church_rosser`. -/
def Diamond {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d

variable {α : Type u} (r : α → α → Prop)
  (wf : WellFounded (fun smaller larger ↦ r larger smaller))

include wf in
theorem exists_normal (a : α) : ∃ n, ReflTransGen r a n ∧ Normal r n := by
  classical
  apply wf.induction a
  intro a ih
  by_cases hn : Normal r a
  · exact ⟨a, ReflTransGen.refl, hn⟩
  · obtain ⟨b, hab⟩ : ∃ b, r a b := by
      exact Classical.not_forall_not.mp hn
    obtain ⟨n, hbn, hn⟩ := ih b hab
    exact ⟨n, (ReflTransGen.single hab).trans hbn, hn⟩

theorem normal_unique (diamond : Diamond r) {a n m : α}
    (han : ReflTransGen r a n) (ham : ReflTransGen r a m)
    (hn : Normal r n) (hm : Normal r m) : n = m := by
  obtain ⟨d, hnd, hmd⟩ := church_rosser diamond han ham
  have hdn : d = n := (reflTransGen_iff_eq hn).mp hnd
  have hdm : d = m := (reflTransGen_iff_eq hm).mp hmd
  exact hdn.symm.trans hdm

/-- A chosen reachable normal form; no inhabitedness premise is needed. -/
noncomputable def normalForm (a : α) : {n // Normal r n} :=
  ⟨Classical.choose (exists_normal r wf a),
    (Classical.choose_spec (exists_normal r wf a)).2⟩

theorem normalForm_reduces (a : α) : ReflTransGen r a (normalForm r wf a).val :=
  (Classical.choose_spec (exists_normal r wf a)).1

theorem normalForm_normal (a : α) : Normal r (normalForm r wf a).val :=
  (normalForm r wf a).property

theorem normalForm_finite (diamond : Diamond r) {a b : α}
    (hab : ReflTransGen r a b) : normalForm r wf a = normalForm r wf b := by
  apply Subtype.ext
  exact normal_unique r diamond (normalForm_reduces r wf a)
    (hab.trans (normalForm_reduces r wf b))
    (normalForm_normal r wf a) (normalForm_normal r wf b)

theorem normalForm_step (diamond : Diamond r) {a b : α} (hab : r a b) :
    normalForm r wf a = normalForm r wf b :=
  normalForm_finite r wf diamond (ReflTransGen.single hab)

theorem normalForm_of_normal (diamond : Diamond r) (n : {n // Normal r n}) :
    normalForm r wf n.val = n := by
  apply Subtype.ext
  exact normal_unique r diamond (normalForm_reduces r wf n.val)
    ReflTransGen.refl (normalForm_normal r wf n.val) n.property

theorem normalForm_idempotent (diamond : Diamond r) (a : α) :
    normalForm r wf (normalForm r wf a).val = normalForm r wf a :=
  normalForm_of_normal r wf diamond (normalForm r wf a)

theorem quot_mk_eq_of_finite {a b : α} (hab : ReflTransGen r a b) :
    Quot.mk r a = Quot.mk r b := by
  apply Quot.eqvGen_sound
  exact reflTransGen_of_equivalence (EqvGen.is_equivalence r)
    (fun a b h ↦ EqvGen.rel a b h) hab

/-- The original quotient and its actual normal representatives, with both inverses. -/
noncomputable def quotientNormalEquiv (diamond : Diamond r) :
    Quot r ≃ {n // Normal r n} where
  toFun := Quot.lift (normalForm r wf) (fun _ _ h ↦ normalForm_step r wf diamond h)
  invFun n := Quot.mk r n.val
  left_inv := by
    intro z
    induction z using Quot.inductionOn with
    | h a =>
      exact (quot_mk_eq_of_finite r (normalForm_reduces r wf a)).symm
  right_inv n := normalForm_of_normal r wf diamond n

@[simp] theorem quotientNormalEquiv_mk (diamond : Diamond r) (a : α) :
    quotientNormalEquiv r wf diamond (Quot.mk r a) = normalForm r wf a := rfl

@[simp] theorem quotientNormalEquiv_symm (diamond : Diamond r) (n : {n // Normal r n}) :
    (quotientNormalEquiv r wf diamond).symm n = Quot.mk r n.val := rfl

theorem quotientNormalEquiv_left_inv (diamond : Diamond r) (z : Quot r) :
    Quot.mk r (quotientNormalEquiv r wf diamond z).val = z :=
  (quotientNormalEquiv r wf diamond).left_inv z

theorem quotientNormalEquiv_right_inv (diamond : Diamond r) (n : {n // Normal r n}) :
    quotientNormalEquiv r wf diamond (Quot.mk r n.val) = n :=
  (quotientNormalEquiv r wf diamond).right_inv n

/-- A map may create reductions: its source steps need only map to finite target steps. -/
theorem normalForm_map {β : Type v} (s : β → β → Prop)
    (ws : WellFounded (fun smaller larger ↦ s larger smaller)) (ds : Diamond s)
    (f : α → β) (hf : ∀ a b, r a b → ReflTransGen s (f a) (f b)) (a : α) :
    normalForm s ws (f (normalForm r wf a).val) = normalForm s ws (f a) := by
  exact (normalForm_finite s ws ds
    (ReflTransGen.lift' f hf (normalForm_reduces r wf a))).symm

end DaggerNormalFormQuotient
