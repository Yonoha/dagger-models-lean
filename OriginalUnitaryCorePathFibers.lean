import OriginalUnitaryCoreCanonicalVertices
import OriginalFullVertexPathFiberModelConsequences

/-!
# Original unitary-core path fibers with the original input vertices as endpoints

The full-subcomplex comparison is applied to the actual unitary-core inclusion.
Both endpoints are the canonical constant homotopy-fixed vertices associated
to the original input vertices. The strict comparison is an isomorphism and a
native weak equivalence. Both endpoint maps are native Kan fibrations and both
strict fibers are fibrant. Identification with the manuscript's derived
equivariant mapping spaces remains a separate requirement.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalDaggerRealizationContinuousAction DaggerOriginalFullVertexSubcomplex
open DaggerOriginalEC2CanonicalVertexSubcomplex DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalUnitaryCorePathFibers

noncomputable section

/-- The original ambient singular equivariant mapping object is native Kan. -/
theorem unitaryCoreAmbient_kan (X : DaggerSSet.{u}) :
    (unitaryCoreAmbientFunctor.obj X).KanComplex :=
  mappingSing_kan (realizedContinuousActionFunctor.obj (daggerCoreCandidate X))

/-- The actual inclusion induces an isomorphism of strict fibers with the same original labels.
-/
def unitaryCorePathFiberIso (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet) ≅
    (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y)) : SSet) :=
  strictPathFiberIso (canonicalVertices (daggerCoreCandidate X))
    (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y)

/-- The forward isomorphism is exactly the map induced by the original unitary-core inclusion.
-/
theorem unitaryCorePathFiberIso_hom (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (unitaryCorePathFiberIso X x y).hom =
      strictPathFiberMap (unitaryCoreInclusion.app X)
        (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) := rfl

/-- The actual strict comparison is a weak equivalence in the native simplicial-set model. -/
theorem unitaryCorePathFiberMap_weakEquivalence (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    WeakEquivalence (strictPathFiberMap (unitaryCoreInclusion.app X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y)) :=
  strictPathFiberMap_weakEquivalence (canonicalVertices (daggerCoreCandidate X))
    (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y)

/-- The paired endpoint evaluation of the original unitary core is a native fibration. -/
theorem unitaryCorePathEndpoint_fibration (X : DaggerSSet.{u}) :
    Fibration (unitaryCore X).pathEv₀₁ := by
  have : (unitaryCore X).KanComplex := unitaryCore_kan X
  exact strictPathEndpoint_fibration (unitaryCore X)

/-- The paired endpoint evaluation in the original ambient is a native fibration. -/
theorem unitaryCoreAmbientPathEndpoint_fibration (X : DaggerSSet.{u}) :
    Fibration (unitaryCoreAmbientFunctor.obj X).pathEv₀₁ := by
  have : (unitaryCoreAmbientFunctor.obj X).KanComplex := unitaryCoreAmbient_kan X
  exact strictPathEndpoint_fibration (unitaryCoreAmbientFunctor.obj X)

/-- The literal unitary-core fiber at the original canonical endpoints is fibrant. -/
theorem unitaryCorePathFiber_fibrant (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    IsFibrant (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet) := by
  have : (unitaryCore X).KanComplex := unitaryCore_kan X
  exact strictPathFiber_fibrant _ _ _

/-- The literal ambient fiber at those same original canonical endpoints is fibrant. -/
theorem unitaryCoreAmbientPathFiber_fibrant (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    IsFibrant (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y)) : SSet) := by
  have : (unitaryCoreAmbientFunctor.obj X).KanComplex := unitaryCoreAmbient_kan X
  exact strictPathFiber_fibrant _ _ _

end

end DaggerOriginalUnitaryCorePathFibers
