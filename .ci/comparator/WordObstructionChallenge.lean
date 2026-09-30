import Mathlib.Data.List.Basic

/-! Trusted specification: the vertex-level word obstruction; no model-structure claim. -/
set_option warningAsError false
namespace DaggerModels.WordObstruction

def dagger (w : List Bool) : List Bool := w.reverse.map Bool.not

theorem dagger_length (w : List Bool) : (dagger w).length = w.length := by sorry

theorem dagger_involutive (w : List Bool) : dagger (dagger w) = w := by sorry

theorem dagger_append (v w : List Bool) : dagger (v ++ w) = dagger w ++ dagger v := by sorry

theorem no_selfAdjoint_length_one {w : List Bool} (h : w.length = 1) :
    dagger w ≠ w := by sorry

theorem no_dagger_preserving_section :
    ¬ ∃ s : Nat → List Bool,
      (∀ n, (s n).length = n) ∧ (∀ n, dagger (s n) = s n) := by sorry

end DaggerModels.WordObstruction
