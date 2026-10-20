import OriginalEC2EndpointCylinders

/-!
# Original unitary recognition through actual equivariant endpoint cylinders

The exact strict unitary path fiber is explicitly identified on vertices with original EC₂
endpoint cylinders. The same chosen ambient replacement fiber has vertices precisely when
these cylinders exist. Together with the already verified original mapping-space criterion,
this recognizes weak equivalence of the same unitary map by actual cylinder coverage.
The rigidification, interval mapping-space, and Dugger--Spivak identifications remain separate.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalFullVertexSubcomplex DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalUnitaryChosenPathComponentRecognition
open DaggerOriginalUnitaryContinuousPaths DaggerOriginalEC2EndpointCylinders
open DaggerOriginalInnerHornFillers DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalUnitaryMappingWeakEquivalenceRecognition

universe u

namespace DaggerOriginalUnitaryCylinderRecognition

noncomputable section

/-- Vertices of the exact original unitary fiber are actual original endpoint cylinders. -/
def unitaryStrictEndpointCylinderEquiv (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet).obj (op ⦋0⦌) ≃
      unitaryEndpointCylinder X x y :=
  (unitaryStrictContinuousPathEquiv X x y).trans
    (pathEndpointCylinderEquiv _ (canonicalCoreConstant X x) (canonicalCoreConstant X y))

/-- The chosen original ambient fiber is nonempty exactly when the original cylinder exists. -/
theorem chosenAmbientPath_vertex_iff_endpointCylinder (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    Nonempty ((chosenAmbientPath X x y).obj (op ⦋0⦌)) ↔
      Nonempty (unitaryEndpointCylinder X x y) :=
  (chosenAmbientPath_vertex_iff_continuousPath X x y).trans
    (pathEndpointCylinderEquiv _ (canonicalCoreConstant X x)
      (canonicalCoreConstant X y)).nonempty_congr

/-- Under the actual original mapping weak equivalences, the same original unitary map is a
 weak equivalence exactly when the actual original endpoint cylinders cover all target vertices.
-/
theorem unitaryCore_map_weakEquivalence_iff_endpointCylinders
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X.toSSet) (hY : innerHornFillers Y.toSSet)
    (hmap : ∀ x y : X.toSSet.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f.hom x y)) :
    WeakEquivalence (unitaryCoreFunctor.map f) ↔
      ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
        Nonempty (unitaryEndpointCylinder Y (f.hom.app (op ⦋0⦌) x) y) :=
  (unitaryCore_map_weakEquivalence_iff_of_mappingWeak f hX hY hmap).trans
    (unitary_components_surjective_iff_endpointCylinders f)

end

end DaggerOriginalUnitaryCylinderRecognition
