import ChosenNecklaceCanonicalComparison

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

theorem code_single_of_no_internal (T : NecklaceCode)
    (h : ∀ j ∈ T.joints, j = 0 ∨ j = Fin.last T.len) : T = single T.len := by
  apply code_ext (T := T) (U := single T.len) rfl
  apply heq_of_eq
  ext j
  constructor
  · intro hj
    exact (mem_single_joints T.len j).mpr (h j hj)
  · intro hj
    rcases (mem_single_joints T.len j).mp hj with he | he
    · exact he ▸ T.first_mem
    · exact he ▸ T.last_mem

/-- Actual internal joint witness; neither point code nor a single bead is omitted. -/
theorem exists_internal_joint (T : NecklaceCode)
    (h : ¬∀ j ∈ T.joints, j = 0 ∨ j = Fin.last T.len) :
    ∃ j ∈ T.joints, 0 < j ∧ j < Fin.last T.len := by
  classical
  push_neg at h
  obtain ⟨j, hj, h0, hn⟩ := h
  exact ⟨j, hj, lt_of_le_of_ne (Fin.zero_le j) h0.symm,
    lt_of_le_of_ne (Fin.le_last j) hn⟩

theorem cutLeft_len_lt (T : NecklaceCode) (j : Fin (T.len + 1))
    (hj : j < Fin.last T.len) : (cutLeft T j).len < T.len := by
  change j.val - 0 < T.len
  change j.val < T.len at hj
  omega

theorem cutRight_len_lt (T : NecklaceCode) (j : Fin (T.len + 1))
    (hj : 0 < j) : (cutRight T j).len < T.len := by
  change T.len - j.val < T.len
  change 0 < j.val at hj
  have hb := j.isLt
  omega

/-- All necklaces, by the same original cut pushouts and both smaller actual interval codes. -/
theorem canonicalComparison_nonempty (T : NecklaceCode) :
    Nonempty (CanonicalComparison.{u} T) := by
  classical
  have h : ∀ n, ∀ U : NecklaceCode, U.len = n → Nonempty (CanonicalComparison.{u} U) := by
    intro n
    induction n using Nat.strong_induction_on with | h n ih
    intro U hn
    by_cases hj : ∀ j ∈ U.joints, j = 0 ∨ j = Fin.last U.len
    · have he := code_single_of_no_internal U hj
      rw [he]
      exact ⟨singleCanonicalComparison _⟩
    · obtain ⟨j, hj, h0, ht⟩ := exists_internal_joint U hj
      obtain ⟨L⟩ := ih (cutLeft U j).len (hn ▸ cutLeft_len_lt U j ht) (cutLeft U j) rfl
      obtain ⟨R⟩ := ih (cutRight U j).len (hn ▸ cutRight_len_lt U j h0) (cutRight U j) rfl
      exact ⟨cutCanonicalComparison U j hj L R⟩
  exact h T.len T rfl

/-- The comparison is constructed, not supplied as a caller hypothesis. -/
def chosenComparison (T : NecklaceCode) : CanonicalComparison.{u} T :=
  Classical.choice (canonicalComparison_nonempty T)

def chosenNecklaceIso (T : NecklaceCode) : C.{u}.obj T.toSSet ≅ NC.{u} T :=
  (chosenComparison T).iso

theorem chosenNecklaceIso_objects (T : NecklaceCode) (a : (C.{u}.obj T.toSSet).Obj) :
    (chosenNecklaceIso T).hom.obj a = canonicalNCObject T a :=
  (chosenComparison T).objects a

theorem chosenNecklaceIso_inv_objects (T : NecklaceCode) (a : (NC.{u} T).Obj) :
    (chosenNecklaceIso T).inv.obj a = RV T.toSSet (T.verticesEquiv.symm a.as) :=
  (chosenComparison T).toLabelledComparison.inverse_object a

theorem chosenNecklaceIso_inclusion (T : NecklaceCode) :
    (chosenNecklaceIso.{u} T).hom ≫ forgetNC T = C.map T.inclusion ≫ (ρ.app ⦋T.len⦌).hom :=
  (chosenComparison T).inclusion

end

end DaggerChosenRigidificationNecklace
