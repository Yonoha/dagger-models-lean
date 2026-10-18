import OriginalEC2Evaluation

/-!
# Original unitary-core evaluation at the identity vertex of original EC₂

The full-subcomplex inclusion is followed by evaluation on the actual
singular equivariant mapping object. Its target is the singular realization
of the same original dagger core. Original canonical vertex labels are sent
to their original realization-singular unit vertices, naturally in dagger maps.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalDaggerCoreCandidateFunctor
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalEC2Evaluation

universe u

namespace DaggerOriginalUnitaryCoreEvaluation

noncomputable section

/-- Evaluate the actual original unitary core at the realized original identity vertex. -/
def unitaryEvaluation (X : DaggerSSet.{u}) :
    unitaryCore X ⟶ TopCat.toSSet.obj (SSet.toTop.obj (daggerCoreCandidate X).toSSet) :=
  unitaryCoreInclusion.app X ≫ daggerEvaluation (daggerCoreCandidate X) identityPoint

/-- The exact original canonical vertex is sent to the original core unit vertex. -/
theorem unitaryEvaluation_canonical (X : DaggerSSet.{u})
    (x : X.toSSet.obj (op ⦋0⦌)) :
    (unitaryEvaluation X).app (op ⦋0⦌) (canonicalUnitaryVertex X x) =
      (sSetTopAdj.unit.app (daggerCoreCandidate X).toSSet).app (op ⦋0⦌)
        ((coreVertexEquiv X).symm x) := by
  change (daggerEvaluation (daggerCoreCandidate X) identityPoint).app (op ⦋0⦌)
    (DaggerOriginalEC2HomotopyFixedPointObject.canonicalZeroSimplex
      (daggerCoreCandidate X) ((coreVertexEquiv X).symm x)) = _
  exact (daggerEvaluation_canonical _ _ _).trans (realizedSingularVertex_eq_unit _ _)

/-- Evaluation commutes with the actual original core map and original unitary map. -/
theorem unitaryEvaluation_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    unitaryCoreFunctor.map f ≫ unitaryEvaluation Y =
      unitaryEvaluation X ≫ TopCat.toSSet.map (SSet.toTop.map (daggerCoreMap f).hom) := by
  unfold unitaryEvaluation
  rw [← Category.assoc, unitaryCoreInclusion.naturality, Category.assoc]
  change unitaryCoreInclusion.app X ≫
    (DaggerOriginalEC2HomotopyFixedPointFunctor.daggerHomotopyFixedPointFunctor.map
      (daggerCoreMap f) ≫ daggerEvaluation (daggerCoreCandidate Y) identityPoint) = _
  rw [daggerEvaluation_naturality]
  simp only [Category.assoc]
  rfl

end

end DaggerOriginalUnitaryCoreEvaluation
