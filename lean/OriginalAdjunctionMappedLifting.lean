import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! Exact transport of right lifting properties through an adjunction, including arrow isos. -/
set_option autoImplicit false
open CategoryTheory
universe u v a b
namespace DaggerOriginalAdjunctionMappedLifting
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]

/-- A right arrow lifts against the mapped class exactly when its right adjoint image lifts. -/
theorem mapped_rlp_eq {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (I : MorphismProperty C) : (I.map L).rlp = I.rlp.inverseImage R := by
  funext X Y p
  apply propext
  constructor
  · intro h A B i hi
    apply (adj.hasLiftingProperty_iff i p).mp
    exact h (L.map i) ⟨A, B, i, hi, ⟨Iso.refl _⟩⟩
  · intro h A B i hi
    rcases hi with ⟨A', B', i', hi', ⟨e⟩⟩
    apply (HasLiftingProperty.iff_of_arrow_iso_left e p).mp
    exact (adj.hasLiftingProperty_iff i' p).mpr (h i' hi')

end DaggerOriginalAdjunctionMappedLifting
