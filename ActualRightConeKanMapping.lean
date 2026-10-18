import ActualRightConeFunctorialComparisons
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! Actual right-cone mapping objects are Kan whenever the original target Homs are Kan. -/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial EnrichedCategory
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitBNextConeEvaluationIndex
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualRightConeKanMapping
noncomputable section

/-- The original right Quillen functor takes every original Kan complex to a Kan complex. -/
theorem singular_Kan (X : SSet.{u}) [X.KanComplex] : (singular.obj X).KanComplex := by
  have : singular.{u}.IsRightAdjoint := ⟨_, ⟨realizationSingularAdjunction⟩⟩
  have : Fibration (singular.map (terminal.from X)) := inferInstance
  have hf : IsFibrant (singular.obj X) :=
    (isFibrant_iff_of_isTerminal (singular.map (terminal.from X))
      (terminalIsTerminal.isTerminalObj singular (⊤_ SSet.{u}))).mpr inferInstance
  infer_instance

/-- The literal right-cone mapping object is Kan for every locally Kan enriched target. -/
theorem rightCone_Kan (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) : (rightConeSimplices D v w).KanComplex := by
  have := hD (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w)
  have := singular_Kan (NerveVertices.vertexEquiv D v ⟶[SSet.{u}] NerveVertices.vertexEquiv D w)
  have hf : IsFibrant (rightConeSimplices D v w) :=
    isFibrant_of_iso (DaggerActualRightConeSingularComparisonIso.comparisonIso D v w).symm
  infer_instance

end
end DaggerActualRightConeKanMapping
