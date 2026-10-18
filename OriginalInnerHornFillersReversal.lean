import OriginalHornFillingReversal
import OriginalInnerHornFillers

/-!
# The exact original inner-horn condition survives native simplicial reversal

Both strict inner-index inequalities are preserved by native finite reversal.
The exact reversed horn map is filled in the original simplicial set through
the native double-opposite iso. The original-map extension transport then
fills the supplied horn in the opposite, in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalHornFillingReversal

universe u

namespace DaggerOriginalInnerHornFillersReversal

noncomputable section

/-- Reversing the original inner index retains both original strict inequalities. -/
theorem reverse_inner_index {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i)
    (hn : i < Fin.last n) : 0 < i.rev ∧ i.rev < Fin.last n := by
  change 0 < i.val at h0
  change i.val < n at hn
  constructor
  · change 0 < i.rev.val
    rw [Fin.val_rev]
    omega
  · change i.rev.val < n
    rw [Fin.val_rev]
    omega

/-- Native simplicial reversal preserves the original inner-horn property in every universe. -/
theorem innerHornFillers_op {X : SSet.{u}} (hX : innerHornFillers X) :
    innerHornFillers X.op := by
  intro n i h0 hn φ
  let ε := SSet.opFunctorCompOpFunctorIso.{u}
  have hi := reverse_inner_index h0 hn
  obtain ⟨τ, hτ⟩ := hX hi.1 hi.2 (reverseHornMap n i φ ≫ ε.hom.app X)
  have hc : ε.inv.app X ≫ ε.hom.app X = 𝟙 X := (ε.app X).inv_hom_id
  have hτ' : reverseHornMap n i φ = Λ[n, i.rev].ι ≫ (τ ≫ ε.inv.app X) := by
    apply (cancel_mono (ε.hom.app X)).mp
    rw [Category.assoc, Category.assoc, hc, Category.comp_id]
    exact hτ
  exact horn_extension_of_reversed_extension n i φ (τ ≫ ε.inv.app X) hτ'

end

end DaggerOriginalInnerHornFillersReversal
