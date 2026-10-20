import OriginalOrdinaryCoreRightOuterHorns
import OriginalInnerHornFillersReversal
import OriginalOrdinaryKanCoreOpposite

/-!
# All original left outer horns fill in the same original ordinary core

Reverse the entire supplied horn, identify the original opposite core with the
core of the original opposite simplicial set, and use the proved original
right outer horn filler. The exact native isomorphisms transfer that filler
back to the entire original horn. No candidate Kan premise is added.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryKanCoreOpposite
open DaggerOriginalInnerHornFillers DaggerOriginalInnerHornFillersReversal
open DaggerOriginalHornFillingReversal DaggerOriginalOrdinaryCoreRightOuterHorns

universe u

namespace DaggerOriginalOrdinaryCoreLeftOuterHorns

noncomputable section

/-- Every original left outer horn in dimension at least two fills in the same original core. -/
theorem core_left_outer_horn_filler (X : SSet.{u}) (hX : innerHornFillers X) (k : ℕ)
    (φ : (Λ[k + 2, 0] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u})) :
    ∃ σ : (Δ[k + 2] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}),
      φ = Λ[k + 2, 0].ι ≫ σ := by
  apply horn_filling_of_reversed_filling (k + 2) 0 _ φ
  have hrev : (0 : Fin (k + 3)).rev = Fin.last (k + 2) := Fin.rev_zero (k + 2)
  rw [hrev]
  intro ψ
  obtain ⟨τ, hτ⟩ := core_right_outer_horn_filler X.op (innerHornFillers_op hX) k
    (ψ ≫ (coreOppositeIso X).hom)
  refine ⟨τ ≫ (coreOppositeIso X).inv, ?_⟩
  apply (cancel_mono (coreOppositeIso X).hom).mp
  rw [Category.assoc, Category.assoc, (coreOppositeIso X).inv_hom_id, Category.comp_id]
  exact hτ

end

end DaggerOriginalOrdinaryCoreLeftOuterHorns
