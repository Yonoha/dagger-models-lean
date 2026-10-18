import OriginalEC2CompactParameterHomEquiv
import OriginalUnitaryContinuousPaths

/-!
# Original EC₂ cylinders with both fixed endpoints

The existing compact-open correspondence is applied to the actual lifted unit interval.
Continuous paths in the original equivariant mapping space correspond to morphisms from the
literal original EC₂ product action whose two endpoint restrictions are the same prescribed
original maps. Applying this correspondence to the canonical core constants gives the endpoint
cylinder form of the original unitary component criterion.
-/

set_option autoImplicit false

open CategoryTheory Topology Opposite Simplicial DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2CompactParameterHomEquiv
open DaggerOriginalUnitaryContinuousPaths DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreCanonicalVertices
open DaggerOriginalUnitaryCoreConstruction

universe u

namespace DaggerOriginalEC2EndpointCylinders

noncomputable section

local instance liftedInterval_compact : CompactSpace TopCat.I.{u} :=
  inferInstanceAs (CompactSpace (ULift.{u} unitInterval))

local instance liftedInterval_t2 : T2Space TopCat.I.{u} :=
  inferInstanceAs (T2Space (ULift.{u} unitInterval))

/-- Actual morphisms from the original EC₂ cylinder, with both original endpoint restrictions. -/
def endpointCylinder (X : ContAction TopCat.{u} C2.{u}) (q₀ q₁ : mappingTop X) :=
  {f : originalEC2Tensor TopCat.I.{u} ⟶ X.obj //
    (∀ e : realizedEC2ContinuousAction.{u}.obj.V, f.hom (e, 0) = q₀.val e) ∧
    (∀ e : realizedEC2ContinuousAction.{u}.obj.V, f.hom (e, 1) = q₁.val e)}

/-- The actual path gives a literal original EC₂ cylinder with the same endpoint values. -/
def cylinderOfPath (X : ContAction TopCat.{u} C2.{u}) {q₀ q₁ : mappingTop X}
    (p : _root_.Path q₀ q₁) : endpointCylinder X q₀ q₁ :=
  ⟨(originalEC2HomEquiv TopCat.I.{u} X).symm
    (TopCat.ofHom (p.toContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩)), by
    constructor
    · intro e
      change (p 0).val e = q₀.val e
      rw [p.source]
    · intro e
      change (p 1).val e = q₁.val e
      rw [p.target]⟩

/-- A literal original endpoint cylinder gives a path in the same original mapping space. -/
def pathOfCylinder (X : ContAction TopCat.{u} C2.{u}) {q₀ q₁ : mappingTop X}
    (f : endpointCylinder X q₀ q₁) : _root_.Path q₀ q₁ where
  toContinuousMap := (originalEC2HomEquiv TopCat.I.{u} X f.val).hom.comp
    ⟨ULift.up, continuous_uliftUp⟩
  source' := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro e
    exact f.property.1 e
  target' := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro e
    exact f.property.2 e

/-- The compact-open correspondence restricts to the exact original two-endpoint cylinders. -/
def pathEndpointCylinderEquiv (X : ContAction TopCat.{u} C2.{u}) (q₀ q₁ : mappingTop X) :
    _root_.Path q₀ q₁ ≃ endpointCylinder X q₀ q₁ where
  toFun := cylinderOfPath X
  invFun := pathOfCylinder X
  left_inv p := by
    apply Path.ext
    funext t
    rfl
  right_inv f := by
    apply Subtype.ext
    ext ⟨e, t⟩
    rfl

/-- The cylinder uses the original core action and the original canonical constant endpoints. -/
abbrev unitaryEndpointCylinder (X : DaggerSSet.{u}) (x y : X.toSSet.obj (op ⦋0⦌)) :=
  endpointCylinder (realizedContinuousActionFunctor.obj (daggerCoreCandidate X))
    (canonicalCoreConstant X x) (canonicalCoreConstant X y)

/-- Original unitary components agree exactly when the same equivariant endpoint cylinder exists.
-/
theorem components_eq_iff_endpointCylinder (X : DaggerSSet.{u})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) ↔
      Nonempty (unitaryEndpointCylinder X x y) :=
  (components_eq_iff_continuousPath X x y).trans
    (pathEndpointCylinderEquiv _ (canonicalCoreConstant X x)
      (canonicalCoreConstant X y)).nonempty_congr

/-- The same original unitary component coverage is expressed by actual endpoint cylinders. -/
theorem unitary_components_surjective_iff_endpointCylinders {X Y : DaggerSSet.{u}}
    (f : X ⟶ Y) :
    Function.Surjective (SSet.mapπ₀ (unitaryCoreFunctor.map f)) ↔
      ∀ y : Y.toSSet.obj (op ⦋0⦌), ∃ x : X.toSSet.obj (op ⦋0⦌),
        Nonempty (unitaryEndpointCylinder Y (f.hom.app (op ⦋0⦌) x) y) := by
  rw [DaggerOriginalUnitaryCoreComponentSurjectivity.unitary_pi0_surjective_iff_canonical]
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_endpointCylinder Y _ y).mp hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, (components_eq_iff_endpointCylinder Y _ y).mpr hx⟩

end

end DaggerOriginalEC2EndpointCylinders
