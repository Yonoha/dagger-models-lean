import OriginalOrdinaryCoreLeftOuterHorns
import OriginalNativeKanFromHornFillers
import OriginalOrdinaryKanCoreContainsKanSubcomplexes

/-!
# The exact original ordinary core is the greatest Kan subcomplex

The original unit-preimage subcomplex fills all actual horns. Inner horns use
the original input condition; both outer horns use the verified original
all-dimensional constructions; one-horns use actual native degenerate edges.
The complete horn condition gives Mathlib's native Kan class. Combining this
with the original containment theorem gives greatest Kan-subcomplex status.
This is the ordinary core, not the final unitary derived-recognition theorem.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreInnerHorns DaggerOriginalOrdinaryCoreRightOuterHorns
open DaggerOriginalOrdinaryCoreLeftOuterHorns DaggerOriginalNativeKanFromHornFillers
open DaggerOriginalOrdinaryKanCoreContainsKanSubcomplexes

universe u

namespace DaggerOriginalOrdinaryCoreKan

noncomputable section

/-- Every original horn of dimension at least two fills in the actual original core. -/
theorem core_horn_filler_of_two_le (X : SSet.{u}) (hX : innerHornFillers X) (k : ℕ)
    (i : Fin (k + 3)) (φ : (Λ[k + 2, i] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u})) :
    ∃ σ : (Δ[k + 2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      φ = Λ[k + 2, i].ι ≫ σ := by
  by_cases h0 : i = 0
  · subst i
    exact core_left_outer_horn_filler X hX k φ
  by_cases hn : i = Fin.last (k + 2)
  · subst i
    exact core_right_outer_horn_filler X hX k φ
  have hi0 : 0 < i := lt_of_le_of_ne (Fin.zero_le i) (Ne.symm h0)
  have hin : i < Fin.last (k + 2) := lt_of_le_of_ne (Fin.le_last i) hn
  exact innerHornFillers_ordinaryCoreCandidate X hX hi0 hin φ

/-- The original core satisfies the complete actual positive-dimensional horn condition. -/
theorem hornFillers_ordinaryCoreCandidate (X : SSet.{u}) (hX : innerHornFillers X) :
    hornFillers (ordinaryCoreCandidate X : SSet.{u}) := by
  intro n i φ
  cases n with
  | zero => exact one_horn_filler i φ
  | succ k => exact core_horn_filler_of_two_le X hX k i φ

/-- The exact original unit-preimage core is a native Kan complex in every universe. -/
theorem ordinaryCoreCandidate_kan (X : SSet.{u}) (hX : innerHornFillers X) :
    (ordinaryCoreCandidate X : SSet.{u}).KanComplex :=
  kanComplex_of_hornFillers (hornFillers_ordinaryCoreCandidate X hX)

/-- The same original core is the greatest native Kan subcomplex of an inner-horn-filling input. -/
theorem ordinaryCoreCandidate_isGreatestKanSubcomplex (X : SSet.{u})
    (hX : innerHornFillers X) :
    IsGreatest {A : X.Subcomplex | (A : SSet.{u}).KanComplex} (ordinaryCoreCandidate X) := by
  refine ⟨ordinaryCoreCandidate_kan X hX, ?_⟩
  intro A hA
  haveI : (A : SSet.{u}).KanComplex := hA
  exact kanSubcomplex_le_ordinaryCoreCandidate X A

end

end DaggerOriginalOrdinaryCoreKan
