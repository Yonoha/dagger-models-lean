import OriginalInnerHornNerveFiller
import OriginalOrdinaryLocalKanReplacement
import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Quasicategory registration for the original ordinary coherent nerve

The previously constructed inner-horn filler registers directly with
Mathlib's quasicategory class. The application to the chosen local Kan
replacement uses its actual output Hom simplicial sets.
-/

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory

noncomputable section

/-- The original ordinary coherent nerve is a quasicategory when every
original Hom simplicial set is Kan. -/
theorem coherentNerve_quasicategory (A : SC.{u})
    (hKan : ∀ x y : A.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    SSet.Quasicategory (N.obj A) := by
  refine ⟨?_⟩
  intro n i a h0 hn
  let k : PathFacets.interior (n + 1) := ⟨i, ⟨h0, hn⟩⟩
  obtain ⟨b, hb⟩ := InnerHornNerveFiller.innerHorn_filling k a hKan
  exact ⟨b, hb.symm⟩

/-- The nerve of the chosen functorial local Kan output is a quasicategory. -/
theorem replacement_quasicategory (C : SC.{u}) :
    SSet.Quasicategory
      (N.obj (DaggerModels.OriginalOrdinaryLocalKanReplacement.replacement.obj C)) := by
  apply coherentNerve_quasicategory
  exact DaggerModels.OriginalOrdinaryLocalKanReplacement.replacement_locallyKan C

end

end DaggerOrdinaryRigidificationCof.OriginalNerveQuasicategory
