import OriginalCompactGenerationSingComparison
import OriginalEC2HomotopyFixedPointFunctor

/-!
# Compact generation of the literal original EC₂ equivariant mapping space

The manuscript's compact-generation step is applied to the original compact-
open equivariance subtype. Its singular complex is naturally isomorphic to the
original singular mapping complex. Canonical vertices are represented by the
same actual constant equivariant maps and are preserved by this comparison.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits DaggerModels Opposite Simplicial Topology
open HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalCompactGeneration DaggerOriginalCompactGenerationSingComparison

universe u

namespace DaggerOriginalEC2MappingCompactGeneration

noncomputable section

/-- The literal original equivariant mapping space followed by Mathlib compact generation. -/
def compactMappingTopFunctor : ContAction TopCat.{u} C2.{u} ⥤ TopCat.{u} :=
  mappingTopFunctor ⋙ compactGenerationTopFunctor

/-- Singular of the compact-generated original mapping-space functor. -/
def compactMappingSingFunctor : ContAction TopCat.{u} C2.{u} ⥤ SSet.{u} :=
  compactMappingTopFunctor ⋙ TopCat.toSSet

/-- The comparison is a natural isomorphism of the actual singular mapping functors. -/
def compactMappingSingIso : compactMappingSingFunctor.{u} ≅ mappingSingFunctor.{u} :=
  Functor.associator mappingTopFunctor compactGenerationTopFunctor TopCat.toSSet ≪≫
    Functor.isoWhiskerLeft mappingTopFunctor compactGenerationSingIso

/-- The comparison is exactly singular of compact generation's native counit. -/
theorem compactMappingSingIso_hom (X : ContAction TopCat.{u} C2.{u}) :
    (compactMappingSingIso.app X).hom =
      TopCat.toSSet.map (compactGenerationCounit.app (mappingTop X)) := by
  ext n t
  rfl

/-- The same original equivariant constant map viewed in the compact-generated topology. -/
def compactCanonicalPoint (K : DaggerSSet.{u}) (x : K.toSSet _⦋0⦌) :
    compactMappingTopFunctor.obj (realizedContinuousActionFunctor.obj K) :=
  (WithGeneratedByTopology.equiv (X := compactHausFamily.{u})).symm
    (DaggerOriginalEC2RealizationAction.canonicalConstantMap K x)

/-- The actual constant singular simplex at the original compact-generated canonical point. -/
def compactCanonicalZeroSimplex (K : DaggerSSet.{u}) (x : K.toSSet _⦋0⦌) :
    (compactMappingSingFunctor.obj (realizedContinuousActionFunctor.obj K)).obj (op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv
    (compactMappingTopFunctor.obj (realizedContinuousActionFunctor.obj K)) (op ⦋0⦌)).symm
      (ContinuousMap.const _ (compactCanonicalPoint K x))

/-- The compact generation counit sends the original canonical point to the identical old map. -/
theorem compactCounit_canonicalPoint (K : DaggerSSet.{u}) (x : K.toSSet _⦋0⦌) :
    (compactGenerationCounit.app (mappingTop (realizedContinuousActionFunctor.obj K)))
      (compactCanonicalPoint K x) =
        DaggerOriginalEC2RealizationAction.canonicalConstantMap K x := rfl

/-- Singular comparison preserves the original canonical vertex with its original label. -/
theorem compactSingIso_canonicalZeroSimplex (K : DaggerSSet.{u}) (x : K.toSSet _⦋0⦌) :
    ((compactMappingSingIso.app (realizedContinuousActionFunctor.obj K)).hom.app (op ⦋0⦌))
      (compactCanonicalZeroSimplex K x) = canonicalZeroSimplex K x := by
  rw [compactMappingSingIso_hom]
  rfl

/-- Inverse singular comparison sends the old canonical vertex to the same generated vertex. -/
theorem compactSingIso_inv_canonicalZeroSimplex (K : DaggerSSet.{u}) (x : K.toSSet _⦋0⦌) :
    ((compactMappingSingIso.app (realizedContinuousActionFunctor.obj K)).inv.app (op ⦋0⦌))
      (canonicalZeroSimplex K x) = compactCanonicalZeroSimplex K x := by
  rw [← compactSingIso_canonicalZeroSimplex K x]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (compactMappingSingIso.app _).hom_inv_id (op ⦋0⦌)) _

/-- Weak equivalence of actual original postcomposition is unchanged by compact generation. -/
theorem compact_postcompose_weakEquivalence_iff
    {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y) :
    WeakEquivalence (compactMappingTopFunctor.map f) ↔ WeakEquivalence (postcompose f) :=
  compactGeneration_weakEquivalence_iff (postcompose f)

/-- Native fibration of actual original postcomposition is unchanged by compact generation. -/
theorem compact_postcompose_fibration_iff
    {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y) :
    Fibration (compactMappingTopFunctor.map f) ↔ Fibration (postcompose f) :=
  compactGeneration_fibration_iff (postcompose f)

end

end DaggerOriginalEC2MappingCompactGeneration
