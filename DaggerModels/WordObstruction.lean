import Std

/-!
# The word obstruction

This proves the algebraic vertex-level obstruction in `dj.prop.counterexample`.
The two vertices of the indiscrete groupoid are represented by `Bool`.
No statement about Kan fibrations or Bergner cofibrations is asserted here.
-/

namespace DaggerModels.WordObstruction

/-- Reverse a word and exchange the two letters. -/
def dagger (w : List Bool) : List Bool := w.reverse.map Bool.not

theorem dagger_length (w : List Bool) : (dagger w).length = w.length := by
  simp [dagger]

theorem dagger_involutive (w : List Bool) : dagger (dagger w) = w := by
  simp [dagger, List.map_reverse, List.map_map, Function.comp_def]

theorem dagger_append (v w : List Bool) : dagger (v ++ w) = dagger w ++ dagger v := by
  simp [dagger]

theorem no_selfAdjoint_length_one {w : List Bool} (h : w.length = 1) :
    dagger w ≠ w := by
  cases w with
  | nil => simp at h
  | cons b w =>
    have hw : w = [] := by simpa using h
    subst w
    cases b <;> simp [dagger]

/-- No section of the length map preserves dagger, even as a function. -/
theorem no_dagger_preserving_section :
    ¬ ∃ s : Nat → List Bool,
      (∀ n, (s n).length = n) ∧ (∀ n, dagger (s n) = s n) := by
  rintro ⟨s, hlength, hdagger⟩
  exact no_selfAdjoint_length_one (hlength 1) (hdagger 1)

end DaggerModels.WordObstruction
