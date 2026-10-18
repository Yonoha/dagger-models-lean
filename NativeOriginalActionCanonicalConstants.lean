import NativeOriginalC2RealizationMapping

/-! Literal original EC2 constant vertices for ORIGINAL action-fixed simplicial vertices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeOriginalC2RealizationMapping DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEquivariantConstantMaps DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
universe u
namespace DaggerNativeOriginalActionCanonicalConstants
noncomputable section

/-- The SAME realized Yoneda vertex, with the SAME original zero-simplex realization point. -/
def realizedVertex (X : SSet.{u}) (x : X _⦋0⦌) : SSet.toTop.obj X :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x)
    ((SSet.toTopSimplex.{u}.inv.app ⦋0⦌) (default : SimplexCategory.toTop.{u}.obj ⦋0⦌))

theorem realizedVertex_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    SSet.toTop.map f (realizedVertex X x) = realizedVertex Y (f.app (op ⦋0⦌) x) := by
  have hv : SSet.yonedaEquiv.symm x ≫ f =
      SSet.yonedaEquiv.symm (f.app (op ⦋0⦌) x) := by
    rw [SSet.yonedaEquiv_symm_comp]
  unfold realizedVertex
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, hv]

/-- A fixed original simplicial vertex gives its SAME strict fixed realized point. -/
def fixedPoint (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g : C2.{u}, (A.ρ g).asHom.app (op ⦋0⦌) x = x) :
    FixedPoints (realizationFunctor.obj A) :=
  ⟨realizedVertex A.V x, by
    intro g
    change SSet.toTop.map (A.ρ g).asHom (realizedVertex A.V x) = realizedVertex A.V x
    rw [realizedVertex_naturality, hx]⟩

/-- Use the OLD literal original EC2 equivariant constant-map construction. -/
def canonicalZero (A : Action SSet.{u} C2.{u}) (x : A.V _⦋0⦌)
    (hx : ∀ g : C2.{u}, (A.ρ g).asHom.app (op ⦋0⦌) x = x) :
    (mappingFunctor.obj A) _⦋0⦌ :=
  (TopCat.toSSetObjEquiv (mappingTop (realizationFunctor.obj A)) (op ⦋0⦌)).symm
    (ContinuousMap.const _ (constantMap realizedEC2ContinuousAction.{u} _ (fixedPoint A x hx)))

/-- Equality of the original simplicial vertices gives equality of the ORIGINAL EC2 constants. -/
theorem canonicalZero_naturality {A B : Action SSet.{u} C2.{u}} (f : A ⟶ B)
    (x : A.V _⦋0⦌) (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x)
    (y : B.V _⦋0⦌) (hy : ∀ g, (B.ρ g).asHom.app (op ⦋0⦌) y = y)
    (hxy : f.hom.app (op ⦋0⦌) x = y) :
    (mappingFunctor.map f).app (op ⦋0⦌) (canonicalZero A x hx) = canonicalZero B y hy := by
  apply (TopCat.toSSetObjEquiv (mappingTop (realizationFunctor.obj B)) (op ⦋0⦌)).injective
  ext t
  apply Subtype.ext
  ext e
  exact (realizedVertex_naturality f.hom x).trans (congrArg (realizedVertex B.V) hxy)

/-- The edgewise endpoint keeps the SAME original geometric vertex. -/
theorem realized_edgewise_vertex_eq (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    realizedVertex (DaggerNativeRealEdgewiseSSet.edgewise.obj X.toSSet)
        (X.toSSet.σ (0 : Fin 1) x) =
      DaggerNativeRealEdgewiseRealizationVertices.edgewiseRealizedVertex X x := rfl

end
end DaggerNativeOriginalActionCanonicalConstants
