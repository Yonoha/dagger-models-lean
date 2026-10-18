import OriginalNecklacePointSimple
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- The same product with a necklace is the pushout of its two actual joint cuts. -/
theorem productCutIsPushout (K : SSet.{u}) (T : NecklaceCode)
    (j : Fin (T.len + 1)) (hj : j ∈ T.joints) :
    IsPushout
      (prod.map (𝟙 K) (pointAt (cutLeft T j) (ULift.up (Fin.last _))))
      (prod.map (𝟙 K) (pointAt (cutRight T j) (ULift.up 0)))
      (prod.map (𝟙 K) (cutLeftι T j))
      (prod.map (𝟙 K) (cutRightι T j)) :=
  (prod.functor.obj K).map_isPushout (cutIsPushout T j hj)

/-- All four maps in the actual product-cut square have the necklace lifting property. -/
theorem productCut_necklaceSimple (K : SSet.{u}) (T : NecklaceCode)
    (j : Fin (T.len + 1)) :
    NecklaceSimple (prod.map (𝟙 K) (pointAt (cutLeft T j) (ULift.up (Fin.last _)))) ∧
    NecklaceSimple (prod.map (𝟙 K) (pointAt (cutRight T j) (ULift.up 0))) ∧
    NecklaceSimple (prod.map (𝟙 K) (cutLeftι T j)) ∧
    NecklaceSimple (prod.map (𝟙 K) (cutRightι T j)) :=
  ⟨productPointAt_necklaceSimple K _ _, productPointAt_necklaceSimple K _ _,
    necklaceSimple_prod _ (cutLeft_necklaceSimple T j) K,
    necklaceSimple_prod _ (cutRight_necklaceSimple T j) K⟩

/-- The four specified maps are also monomorphisms, with no orderedness premise on K. -/
theorem productCut_mono (K : SSet.{u}) (T : NecklaceCode) (j : Fin (T.len + 1)) :
    Mono (prod.map (𝟙 K) (pointAt (cutLeft T j) (ULift.up (Fin.last _)))) ∧
    Mono (prod.map (𝟙 K) (pointAt (cutRight T j) (ULift.up 0))) ∧
    Mono (prod.map (𝟙 K) (cutLeftι T j)) ∧
    Mono (prod.map (𝟙 K) (cutRightι T j)) := by
  have : Mono (pointAt (cutLeft T j) (ULift.up (Fin.last _))) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  have : Mono (pointAt (cutRight T j) (ULift.up 0)) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  have : Mono (cutLeftι.{u} T j) := by
    dsimp [cutLeftι]
    infer_instance
  have : Mono (cutRightι.{u} T j) := by
    dsimp [cutRightι]
    infer_instance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end

end DaggerOriginalProductGadget
