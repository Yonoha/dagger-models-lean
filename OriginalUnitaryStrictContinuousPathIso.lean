import OriginalSingularStrictContinuousPathIso
import OriginalUnitaryCylinderRecognition

/-!
# Original unitary strict fibers and singular of the original continuous path space

The actual full-subcomplex unitary path-fiber isomorphism is composed with the natural original
singular endpoint-fiber isomorphism. Both endpoints are precisely the original canonical
constant equivariant maps. The inverses give concrete weak-equivalence maps from this same
singular continuous path space to the same already chosen ambient and unitary replacement fibers.
The enriched dagger interval and rigidification comparisons remain separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalFullVertexSubcomplex DaggerOriginalDaggerCoreCandidate
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalUnitaryCorePathFibers DaggerOriginalUnitaryCoreChosenDerivedPaths
open DaggerOriginalUnitaryChosenPathComponentRecognition DaggerOriginalUnitaryContinuousPaths
open DaggerOriginalSingularStrictContinuousPathIso DaggerOriginalContinuousEndpointCylinderFamilies
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalUnitaryStrictContinuousPathIso

noncomputable section

/-- Singular of the original continuous paths between the same original canonical constants. -/
def continuousUnitaryPathSing (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{u} :=
  TopCat.toSSet.obj
    (continuousPathTop (mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)))
      (canonicalCoreConstant X x) (canonicalCoreConstant X y))

/-- The literal original ambient endpoint fiber is singular of these exact continuous paths. -/
def ambientStrictContinuousPathIso (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y)) : SSet) ≅
      continuousUnitaryPathSing X x y := by
  have h := singularStrictContinuousPathIso
    (mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)))
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y))
  simpa only [canonicalZeroSimplex_point, canonicalCoreConstant, continuousUnitaryPathSing] using h

/-- The actual original unitary strict path fiber is simplicially isomorphic to singular of the
 original continuous equivariant mapping-space paths at the same original canonical constants. -/
def unitaryStrictContinuousPathIso (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet) ≅
      continuousUnitaryPathSing X x y :=
  unitaryCorePathFiberIso X x y ≪≫ ambientStrictContinuousPathIso X x y

/-- The same original singular continuous path space is native Kan. -/
instance continuousUnitaryPathSing_kan (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) : (continuousUnitaryPathSing X x y).KanComplex := by
  unfold continuousUnitaryPathSing
  infer_instance

/-- The actual unitary strict-fiber comparison is a native simplicial weak equivalence. -/
theorem unitaryStrictContinuousPathIso_hom_weakEquivalence (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (unitaryStrictContinuousPathIso X x y).hom := by
  infer_instance

/-- The concrete map to the same chosen original ambient replacement path fiber. -/
def continuousPathToChosenAmbient (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    continuousUnitaryPathSing X x y ⟶ chosenAmbientPath X x y :=
  (ambientStrictContinuousPathIso X x y).inv ≫ targetStrictComparison X x y

/-- The concrete map to the same chosen original unitary replacement path fiber. -/
def continuousPathToChosenUnitary (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    continuousUnitaryPathSing X x y ⟶ chosenUnitaryPath X x y :=
  (unitaryStrictContinuousPathIso X x y).inv ≫ sourceStrictComparison X x y

/-- The same concrete ambient replacement comparison is a native weak equivalence. -/
theorem continuousPathToChosenAmbient_weakEquivalence (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (continuousPathToChosenAmbient X x y) := by
  haveI := targetStrictComparison_weakEquivalence X x y
  unfold continuousPathToChosenAmbient
  infer_instance

/-- The same concrete unitary replacement comparison is a native weak equivalence. -/
theorem continuousPathToChosenUnitary_weakEquivalence (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (continuousPathToChosenUnitary X x y) := by
  haveI := sourceStrictComparison_weakEquivalence X x y
  unfold continuousPathToChosenUnitary
  infer_instance

end

end DaggerOriginalUnitaryStrictContinuousPathIso
