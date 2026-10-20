import OriginalEC2HomotopyFixedPointObject

/-!
# Functoriality of the literal EC₂ equivariant mapping object

Postcomposition by a continuous equivariant map acts continuously on the
subspace compact-open equivariant mapping space. Applying singular gives the
point-set functor appearing in the manuscript's formula for (K^{hC_2}).
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEquivariantConstantMaps
open DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject

universe u

namespace DaggerOriginalEC2HomotopyFixedPointFunctor

noncomputable section

/-- Postcomposition on the actual equivariant compact-open mapping spaces. -/
def postcompose {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y) :
    mappingTop X ⟶ mappingTop Y :=
  TopCat.ofHom ⟨fun q ↦
      ⟨f.hom.hom.hom.comp q.val, by
        intro g e
        change f.hom.hom.hom (q.val
          ((realizedEC2ContinuousAction.{u}.obj.ρ g).asHom e)) =
          (Y.obj.ρ g).asHom (f.hom.hom.hom (q.val e))
        rw [q.property g e]
        have hc := f.hom.comm g
        exact congrArg
          (fun t : X.obj.V ⟶ Y.obj.V ↦ t (q.val e)) hc⟩,
    (ContinuousMap.continuous_postcomp f.hom.hom.hom).comp
      continuous_subtype_val |>.subtype_mk _⟩

/-- Equivariant compact-open maps from the literal original EC₂ form a
covariant topological functor in the target action. -/
def mappingTopFunctor : ContAction TopCat.{u} C2.{u} ⥤ TopCat.{u} where
  obj := mappingTop
  map := postcompose
  map_id X := by
    ext q
    rfl
  map_comp f g := by
    ext q
    rfl

/-- The actual singular equivariant mapping complex, functorially. -/
def mappingSingFunctor : ContAction TopCat.{u} C2.{u} ⥤ SSet.{u} :=
  mappingTopFunctor.{u} ⋙ TopCat.toSSet.{u}

/-- The literal point-set construction for dagger simplicial sets. -/
def daggerHomotopyFixedPointFunctor : DaggerSSet.{u} ⥤ SSet.{u} :=
  realizedContinuousActionFunctor ⋙ mappingSingFunctor.{u}

end

end DaggerOriginalEC2HomotopyFixedPointFunctor
