import ProofActualFibrantGadgets
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! Any map from a Kan complex to a degreewise subsingleton simplicial set is a fibration. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerNativeKanFibrationToSubsingleton
noncomputable section

/-- Degreewise subsingleton targets have at most one whole simplicial map from any source. -/
theorem hom_subsingleton (Y : SSet.{u}) (hY : ∀ q, Subsingleton (Y.obj q))
    (Z : SSet.{u}) : Subsingleton (Z ⟶ Y) := by
  refine ⟨fun f g ↦ ?_⟩
  apply NatTrans.ext
  funext q z
  have := hY q
  exact Subsingleton.elim _ _

/-- Native horn lifting uses source Kan filling; the entire target equation follows from thinness. -/
theorem fibration {X Y : SSet.{u}} (p : X ⟶ Y) (hX : SSet.KanComplex X)
    (hY : ∀ q, Subsingleton (Y.obj q)) : Fibration p := by
  have : SSet.KanComplex X := hX
  apply (SSet.modelCategoryQuillen.fibration_iff p).mpr
  intro A B i hi
  rw [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  rcases hi with ⟨n, hi⟩
  cases hi with
  | mk j =>
    refine ⟨fun {f g} sq ↦ ?_⟩
    have hp : Fibration (toUnit X) :=
      (isFibrant_iff_of_isTerminal (toUnit X) isTerminalTensorUnit).mp inferInstance
    have hl : HasLiftingProperty (SSet.horn.{u} (n + 1) j).ι (toUnit X) :=
      (SSet.modelCategoryQuillen.fibration_iff _).mp hp _
        (SSet.modelCategoryQuillen.horn_ι_mem_J n j)
    let sq' : CommSq f (SSet.horn.{u} (n + 1) j).ι (toUnit X)
        (toUnit (Δ[n + 1] : SSet.{u})) :=
      ⟨isTerminalTensorUnit.hom_ext _ _⟩
    have : sq'.HasLift := hl.sq_hasLift sq'
    have : Subsingleton ((Δ[n + 1] : SSet.{u}) ⟶ Y) := hom_subsingleton Y hY _
    exact CommSq.HasLift.mk'
      { l := sq'.lift, fac_left := sq'.fac_left, fac_right := Subsingleton.elim _ _ }

end
end DaggerNativeKanFibrationToSubsingleton
