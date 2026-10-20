import OriginalDaggerRealizationContinuousAction
import Mathlib.Topology.CompactOpen

/-!
# Continuous equivariant constant maps from literal fixed points

The mapping space is the equivariance subtype of Mathlib's compact-open
continuous-map space. The domain is any continuous C₂-action. This is a
general ingredient of the manuscript's strict-to-homotopy-fixed-point map;
no particular EC₂ or compactly generated mapping-space comparison is assumed.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalDaggerRealizationVertices
open DaggerOriginalDaggerRealizationContinuousAction

universe u

namespace DaggerOriginalEquivariantConstantMaps

noncomputable section

/-- The literal fixed-point subtype, with its inherited topology. -/
def FixedPoints (X : ContAction TopCat.{u} C2.{u}) :=
  {x : X.obj.V // ∀ g : C2.{u}, (X.obj.ρ g).asHom x = x}

instance fixedPointsTopology (X : ContAction TopCat.{u} C2.{u}) :
    TopologicalSpace (FixedPoints X) := inferInstanceAs (TopologicalSpace {x : X.obj.V //
      ∀ g : C2.{u}, (X.obj.ρ g).asHom x = x})

/-- Equivariant maps with the subspace compact-open topology. -/
def EquivariantMaps (E X : ContAction TopCat.{u} C2.{u}) :=
  {f : C(E.obj.V, X.obj.V) //
    ∀ (g : C2.{u}) (e : E.obj.V),
      f ((E.obj.ρ g).asHom e) = (X.obj.ρ g).asHom (f e)}

instance equivariantMapsTopology (E X : ContAction TopCat.{u} C2.{u}) :
    TopologicalSpace (EquivariantMaps E X) := inferInstanceAs
      (TopologicalSpace {f : C(E.obj.V, X.obj.V) //
        ∀ (g : C2.{u}) (e : E.obj.V),
          f ((E.obj.ρ g).asHom e) = (X.obj.ρ g).asHom (f e)})

/-- A strict fixed point determines an actual equivariant continuous constant map. -/
def constantMap (E X : ContAction TopCat.{u} C2.{u})
    (x : FixedPoints X) : EquivariantMaps E X :=
  ⟨ContinuousMap.const E.obj.V x.val, fun g _ ↦ (x.property g).symm⟩

/-- The constant-map construction is continuous in the fixed point. -/
theorem constantMap_continuous (E X : ContAction TopCat.{u} C2.{u}) :
    Continuous (constantMap E X) :=
  (ContinuousMap.continuous_const'.comp continuous_subtype_val).subtype_mk _

/-- Evaluation of the constant map returns the same original point. -/
theorem constantMap_apply (E X : ContAction TopCat.{u} C2.{u})
    (x : FixedPoints X) (e : E.obj.V) : (constantMap E X x).val e = x.val := rfl

/-- Every original realized vertex determines its literal strict fixed point. -/
def realizedFixedPoint (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    FixedPoints (realizedContinuousActionFunctor.obj X) :=
  ⟨realizedVertex X x, realizedContinuousVertex_fixed X x⟩

/-- The canonical equivariant constant map associated to an original vertex. -/
def canonicalConstantMap (E : ContAction TopCat.{u} C2.{u})
    (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    EquivariantMaps E (realizedContinuousActionFunctor.obj X) :=
  constantMap E _ (realizedFixedPoint X x)

/-- Its value is the original realized vertex, without a replacement. -/
theorem canonicalConstantMap_apply (E : ContAction TopCat.{u} C2.{u})
    (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) (e : E.obj.V) :
    (canonicalConstantMap E X x).val e = realizedVertex X x := rfl

/-- Postcomposing a vertex constant map is the constant map at the image vertex. -/
theorem canonicalConstantMap_naturality (E : ContAction TopCat.{u} C2.{u})
    {X Y : DaggerSSet.{u}} (f : X ⟶ Y) (x : X.toSSet _⦋0⦌) :
    (SSet.toTop.map f.hom).hom.comp (canonicalConstantMap E X x).val =
      (canonicalConstantMap E Y (f.hom.app (op ⦋0⦌) x)).val := by
  ext e
  change (SSet.toTop.map f.hom) (realizedVertex X x) =
    realizedVertex Y (f.hom.app (op ⦋0⦌) x)
  have hv : vertexMap X x ≫ f.hom =
      vertexMap Y (f.hom.app (op ⦋0⦌) x) := by
    apply SSet.yonedaEquiv.injective
    simp only [vertexMap, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  unfold realizedVertex
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hv]

end

end DaggerOriginalEquivariantConstantMaps
