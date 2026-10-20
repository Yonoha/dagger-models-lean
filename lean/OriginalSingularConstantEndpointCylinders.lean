import OriginalStrictPathFiberHomEquiv
import OriginalUnitaryContinuousPaths

/-!
# The original constant endpoints in every simplicial degree

The native realization-singular adjunction sends the actual singular constant map to the same
actual topological constant map. Thus the original singular strict endpoint fibers, and the
original unitary strict endpoint fibers through their existing full-subcomplex isomorphism,
are identified degree by degree with realized cylinders at the literal original constants.
Naturality and assembly into singular of the continuous path space remain separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerOriginalFullVertexSubcomplex DaggerOriginalStrictPathFiberHomEquiv
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalUnitaryCorePathFibers DaggerOriginalUnitaryContinuousPaths
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalDaggerCoreCandidate
open DaggerOriginalDaggerRealizationContinuousAction DaggerModels

universe u

namespace DaggerOriginalSingularConstantEndpointCylinders

noncomputable section

/-- The original simplicial constant map corresponds to the same original topological constant.
-/
theorem topologicalAdjoint_const (T : TopCat.{u}) (A : SSet.{u})
    (a : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (sSetTopAdj.homEquiv A T).symm (SSet.const a) =
      TopCat.const (X := SSet.toTop.obj A) (TopCat.toSSetObj₀Equiv a) := by
  apply (sSetTopAdj.homEquiv A T).injective
  simp only [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, TopCat.toSSet_map_const,
    Equiv.symm_apply_apply, SSet.comp_const]

/-- For every original parameter, strict singular paths are cylinders at the original points. -/
def singularStrictFiberConstantCylinderEquiv (T : TopCat.{u}) (A : SSet.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) ≃
    {h : SSet.toTop.obj A ⊗ TopCat.I ⟶ T //
      TopCat.ι₀ ≫ h = TopCat.const (TopCat.toSSetObj₀Equiv a) ∧
      TopCat.ι₁ ≫ h = TopCat.const (TopCat.toSSetObj₀Equiv b)} := by
  simpa only [topologicalAdjoint_const] using singularStrictFiberHomCylinderEquiv T A a b

/-- Every original singular strict fiber simplex is a cylinder at the same original points. -/
def singularStrictFiberSimplexConstantCylinderEquiv (T : TopCat.{u}) (n : SimplexCategory)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (strictPathFiber (TopCat.toSSet.obj T) a b : SSet).obj (op n) ≃
    {h : SSet.toTop.obj (SSet.stdSimplex.obj n) ⊗ TopCat.I ⟶ T //
      TopCat.ι₀ ≫ h = TopCat.const (TopCat.toSSetObj₀Equiv a) ∧
      TopCat.ι₁ ≫ h = TopCat.const (TopCat.toSSetObj₀Equiv b)} :=
  SSet.yonedaEquiv.symm.trans
    (singularStrictFiberConstantCylinderEquiv T (SSet.stdSimplex.obj n) a b)

/-- In every degree, the original unitary strict fiber simplices are cylinders in the original
 equivariant mapping space, with the literal original canonical constants as both endpoints. -/
def unitaryStrictSimplexConstantCylinderEquiv (X : DaggerSSet.{u}) (n : SimplexCategory)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet).obj (op n) ≃
    {h : SSet.toTop.obj (SSet.stdSimplex.obj n) ⊗ TopCat.I ⟶
      mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)) //
      TopCat.ι₀ ≫ h = TopCat.const (canonicalCoreConstant X x) ∧
      TopCat.ι₁ ≫ h = TopCat.const (canonicalCoreConstant X y)} := by
  have h := SSet.yonedaEquiv.symm.trans
    ((Iso.homToEquiv (unitaryCorePathFiberIso X x y)).trans
      (singularStrictFiberConstantCylinderEquiv
        (mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)))
        (SSet.stdSimplex.obj n)
        (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
        (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y))))
  simpa only [canonicalZeroSimplex_point, canonicalCoreConstant] using h

end

end DaggerOriginalSingularConstantEndpointCylinders
