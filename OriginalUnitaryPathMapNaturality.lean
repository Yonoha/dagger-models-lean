import OriginalLabeledPathFiberNaturality

/-!
# Naturality of the original unitary continuous path comparison

The actual dagger morphism induces postcomposition on the original equivariant mapping space.
It preserves the canonical constants attached to the original vertices. The original ambient
and full unitary strict path-fiber isomorphisms commute with this same map and these same labels.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalDaggerRealizationContinuousAction DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2CanonicalVertexSubcomplex DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalUnitaryCorePathFibers
open DaggerOriginalUnitaryContinuousPaths DaggerOriginalFullVertexSubcomplex
open DaggerOriginalContinuousEndpointCylinderFamilies DaggerOriginalSingularStrictContinuousPathIso
open DaggerOriginalSingularPathTargetNaturality DaggerOriginalLabeledPathFiberNaturality
open DaggerOriginalUnitaryStrictContinuousPathIso

universe u

namespace DaggerOriginalUnitaryPathMapNaturality

noncomputable section

/-- Actual postcomposition by the realized original dagger core map. -/
def originalCoreMappingTopMap {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)) ⟶
      mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate Y)) :=
  postcompose (realizedContinuousActionFunctor.map (daggerCoreMap f))

/-- The singular map preserves the original canonical zero-simplex labels. -/
theorem coreCanonicalZeroSimplex_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x : X.toSSet.obj (op ⦋0⦌)) :
    (TopCat.toSSet.map (originalCoreMappingTopMap f)).app (op ⦋0⦌)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x)) =
    canonicalZeroSimplex (daggerCoreCandidate Y)
      ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x)) := by
  change (daggerHomotopyFixedPointFunctor.map (daggerCoreMap f)).app (op ⦋0⦌) _ = _
  rw [canonicalZeroSimplex_naturality, coreVertexEquiv_naturality]

/-- The same topological postcomposition preserves the exact original canonical constants. -/
theorem canonicalCoreConstant_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x : X.toSSet.obj (op ⦋0⦌)) :
    originalCoreMappingTopMap f (canonicalCoreConstant X x) =
      canonicalCoreConstant Y (f.hom.app (op ⦋0⦌) x) := by
  have h := congrArg TopCat.toSSetObj₀Equiv (coreCanonicalZeroSimplex_naturality f x)
  simpa only [singularPoint_map, canonicalZeroSimplex_point, canonicalCoreConstant] using h

/-- The original continuous path map at the actual original image vertices. -/
def continuousUnitaryPathTopMap {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    continuousPathTop _ (canonicalCoreConstant X x) (canonicalCoreConstant X y) ⟶
      continuousPathTop _ (canonicalCoreConstant Y (f.hom.app (op ⦋0⦌) x))
        (canonicalCoreConstant Y (f.hom.app (op ⦋0⦌) y)) :=
  labeledContinuousPathTopMap (originalCoreMappingTopMap f)
    (canonicalCoreConstant X x) (canonicalCoreConstant X y)
    (canonicalCoreConstant Y (f.hom.app (op ⦋0⦌) x))
    (canonicalCoreConstant Y (f.hom.app (op ⦋0⦌) y))
    (canonicalCoreConstant_naturality f x) (canonicalCoreConstant_naturality f y)

/-- Singular of that same original continuous path postcomposition. -/
def continuousUnitaryPathSingMap {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    continuousUnitaryPathSing X x y ⟶
      continuousUnitaryPathSing Y (f.hom.app (op ⦋0⦌) x) (f.hom.app (op ⦋0⦌) y) :=
  TopCat.toSSet.map (continuousUnitaryPathTopMap f x y)

/-- The actual unitary strict-fiber map at the original image vertex labels. -/
def unitaryStrictPathFiberMap {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet) ⟶
    (strictPathFiber (unitaryCore Y)
      (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) x))
      (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) y)) : SSet) :=
  labeledStrictPathFiberMap (unitaryCoreFunctor.map f)
    (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y)
    (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) x))
    (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) y))
    (canonicalUnitaryVertex_naturality f x) (canonicalUnitaryVertex_naturality f y)

/-- The original ambient strict-fiber map at precisely the same original image labels. -/
def ambientStrictPathFiberMap {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y)) : SSet) ⟶
    (strictPathFiber (unitaryCoreAmbientFunctor.obj Y)
      (canonicalZeroSimplex (daggerCoreCandidate Y)
        ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x)))
      (canonicalZeroSimplex (daggerCoreCandidate Y)
        ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) y))) : SSet) :=
  labeledStrictPathFiberMap (TopCat.toSSet.map (originalCoreMappingTopMap f))
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y))
    (canonicalZeroSimplex (daggerCoreCandidate Y)
      ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x)))
    (canonicalZeroSimplex (daggerCoreCandidate Y)
      ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) y)))
    (coreCanonicalZeroSimplex_naturality f x) (coreCanonicalZeroSimplex_naturality f y)

/-- The original ambient continuous path isomorphism commutes with the actual dagger map. -/
theorem ambientStrictContinuousPathIso_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ambientStrictPathFiberMap f x y ≫
      (ambientStrictContinuousPathIso Y
        (f.hom.app (op ⦋0⦌) x) (f.hom.app (op ⦋0⦌) y)).hom =
    (ambientStrictContinuousPathIso X x y).hom ≫ continuousUnitaryPathSingMap f x y := by
  exact singularStrictContinuousPathIso_labeled_naturality (originalCoreMappingTopMap f)
    _ _ _ _ (coreCanonicalZeroSimplex_naturality f x) (coreCanonicalZeroSimplex_naturality f y)

/-- Forgetting the strict-fiber condition gives the same unitary internal-hom map. -/
@[reassoc]
theorem unitaryStrictPathFiberMap_ι {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    unitaryStrictPathFiberMap f x y ≫
      (strictPathFiber (unitaryCore Y)
        (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) x))
        (canonicalUnitaryVertex Y (f.hom.app (op ⦋0⦌) y))).ι =
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y)).ι ≫
      (ihom Δ[1]).map (unitaryCoreFunctor.map f) :=
  labeledStrictPathFiberMap_ι _ _ _ _ _ _ _

/-- Forgetting the strict-fiber condition gives the same ambient internal-hom map. -/
@[reassoc]
theorem ambientStrictPathFiberMap_ι {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ambientStrictPathFiberMap f x y ≫
      (strictPathFiber (unitaryCoreAmbientFunctor.obj Y)
        (canonicalZeroSimplex (daggerCoreCandidate Y)
          ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x)))
        (canonicalZeroSimplex (daggerCoreCandidate Y)
          ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) y)))).ι =
    (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y))).ι ≫
      (ihom Δ[1]).map (unitaryCoreAmbientFunctor.map f) :=
  labeledStrictPathFiberMap_ι _ _ _ _ _ _ _

/-- The full-subcomplex path isomorphism is induced by the literal original inclusion. -/
@[reassoc]
theorem unitaryCorePathFiberIso_hom_ι (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (unitaryCorePathFiberIso X x y).hom ≫
      (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
        (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
        (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y))).ι =
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y)).ι ≫
      (ihom Δ[1]).map (unitaryCoreInclusion.app X) := by
  rw [unitaryCorePathFiberIso_hom]
  exact SSet.Subcomplex.lift_ι _ _

/-- The actual full-subcomplex fiber isomorphism commutes with the original dagger map. -/
theorem unitaryCorePathFiberIso_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    unitaryStrictPathFiberMap f x y ≫
      (unitaryCorePathFiberIso Y (f.hom.app (op ⦋0⦌) x) (f.hom.app (op ⦋0⦌) y)).hom =
    (unitaryCorePathFiberIso X x y).hom ≫ ambientStrictPathFiberMap f x y := by
  apply (cancel_mono (strictPathFiber (unitaryCoreAmbientFunctor.obj Y)
    (canonicalZeroSimplex (daggerCoreCandidate Y)
      ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) x)))
    (canonicalZeroSimplex (daggerCoreCandidate Y)
      ((coreVertexEquiv Y).symm (f.hom.app (op ⦋0⦌) y)))).ι).1
  simp only [Category.assoc, unitaryCorePathFiberIso_hom_ι,
    unitaryStrictPathFiberMap_ι_assoc, ambientStrictPathFiberMap_ι,
    unitaryCorePathFiberIso_hom_ι_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, unitaryCoreInclusion.naturality f]

/-- The full original unitary continuous path isomorphism is natural for original dagger maps.
-/
theorem unitaryStrictContinuousPathIso_naturality {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    unitaryStrictPathFiberMap f x y ≫
      (unitaryStrictContinuousPathIso Y
        (f.hom.app (op ⦋0⦌) x) (f.hom.app (op ⦋0⦌) y)).hom =
    (unitaryStrictContinuousPathIso X x y).hom ≫ continuousUnitaryPathSingMap f x y := by
  change unitaryStrictPathFiberMap f x y ≫
      ((unitaryCorePathFiberIso Y _ _).hom ≫ (ambientStrictContinuousPathIso Y _ _).hom) =
    ((unitaryCorePathFiberIso X x y).hom ≫ (ambientStrictContinuousPathIso X x y).hom) ≫ _
  rw [← Category.assoc, unitaryCorePathFiberIso_naturality, Category.assoc,
    ambientStrictContinuousPathIso_naturality, Category.assoc]

end

end DaggerOriginalUnitaryPathMapNaturality
