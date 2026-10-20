import OriginalSingularStrictPaths
import OriginalUnitaryChosenPathComponentRecognition

/-!
# Continuous paths between the original constant equivariant maps

The original full unitary-core inclusion and the native singular path equivalence identify
actual strict unitary path vertices with continuous paths in the original equivariant mapping
space. The endpoints are exactly the original canonical constant maps from realized EC₂.
The chosen replacement path fibers consequently have vertices exactly when these paths exist.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalFullVertexSubcomplex DaggerOriginalDaggerCoreCandidate
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEquivariantConstantMaps
open DaggerOriginalDaggerRealizationContinuousAction DaggerOriginalEC2RealizationAction
open DaggerOriginalUnitaryCoreConstruction DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalUnitaryCorePathFibers DaggerOriginalUnitaryChosenPathComponentRecognition
open DaggerOriginalSingularStrictPaths

universe u

namespace DaggerOriginalUnitaryContinuousPaths

noncomputable section

/-- Native singular zero-simplex evaluation retains the exact original constant map. -/
theorem canonicalZeroSimplex_point (K : DaggerSSet.{u}) (x : K.toSSet.obj (op ⦋0⦌)) :
    TopCat.toSSetObj₀Equiv (canonicalZeroSimplex K x) =
      canonicalConstantMap realizedEC2ContinuousAction K x := by
  change (TopCat.toSSetObjEquiv _ _
    ((TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ _))) default = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The actual constant equivariant map attached to the same original input vertex. -/
def canonicalCoreConstant (X : DaggerSSet.{u}) (x : X.toSSet.obj (op ⦋0⦌)) :
    mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)) :=
  canonicalConstantMap realizedEC2ContinuousAction (daggerCoreCandidate X)
    ((coreVertexEquiv X).symm x)

/-- The actual continuous path space in the original ambient equivariant mapping space. -/
abbrev continuousUnitaryPath (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :=
  _root_.Path (canonicalCoreConstant X x) (canonicalCoreConstant X y)

/-- The original strict unitary fiber and original ambient fiber have the same vertices. -/
def unitaryAmbientStrictVertexEquiv (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet).obj (op ⦋0⦌) ≃
    (strictPathFiber (unitaryCoreAmbientFunctor.obj X)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y)) :
        SSet).obj (op ⦋0⦌) where
  toFun := (unitaryCorePathFiberIso X x y).hom.app (op ⦋0⦌)
  invFun := (unitaryCorePathFiberIso X x y).inv.app (op ⦋0⦌)
  left_inv v := congrFun (NatTrans.congr_app (unitaryCorePathFiberIso X x y).hom_inv_id
    (op ⦋0⦌)) v
  right_inv v := congrFun (NatTrans.congr_app (unitaryCorePathFiberIso X x y).inv_hom_id
    (op ⦋0⦌)) v

/-- Vertices of the exact original unitary fiber are continuous paths between original constants.
-/
def unitaryStrictContinuousPathEquiv (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (strictPathFiber (unitaryCore X)
      (canonicalUnitaryVertex X x) (canonicalUnitaryVertex X y) : SSet).obj (op ⦋0⦌) ≃
      continuousUnitaryPath X x y := by
  refine (unitaryAmbientStrictVertexEquiv X x y).trans ?_
  have h := singularStrictPathVertexEquiv
    (mappingTop (realizedContinuousActionFunctor.obj (daggerCoreCandidate X)))
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x))
    (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm y))
  simpa only [canonicalZeroSimplex_point, continuousUnitaryPath, canonicalCoreConstant] using h

/-- Canonical unitary components agree exactly when the original continuous path exists. -/
theorem components_eq_iff_continuousPath (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) ↔
      Nonempty (continuousUnitaryPath X x y) :=
  (components_eq_iff_strictPath_vertex X x y).trans
    (unitaryStrictContinuousPathEquiv X x y).nonempty_congr

/-- The same chosen ambient replacement fiber has a vertex exactly when this path exists. -/
theorem chosenAmbientPath_vertex_iff_continuousPath (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    Nonempty ((chosenAmbientPath X x y).obj (op ⦋0⦌)) ↔
      Nonempty (continuousUnitaryPath X x y) :=
  (components_eq_iff_chosenAmbientPath_vertex X x y).symm.trans
    (components_eq_iff_continuousPath X x y)

/-- Original unitary component coverage is existence of these exact original continuous paths.
-/
theorem unitary_components_surjective_iff_continuousPaths {X Y : DaggerSSet.{u}}
    (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) ↔
      ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
        Nonempty (continuousUnitaryPath Y (f.hom.app (op ⦋0⦌) x) y) := by
  rw [DaggerOriginalUnitaryCoreComponentSurjectivity.unitary_pi0_surjective_iff_canonical]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_continuousPath Y _ y).mp hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_continuousPath Y _ y).mpr hx⟩

end

end DaggerOriginalUnitaryContinuousPaths
