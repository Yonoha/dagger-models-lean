import ActualIteratedGadgetProperties
import ProofActualConeIndexWeakness

/-! The original rigidification Hom weights of all actual iterated gadgets, with both endpoints. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerActualIteratedGadgetData DaggerChosenRigidificationNecklace
open DaggerOriginalProductGadget hiding Code
open DaggerSSetGluing
universe u
namespace DaggerActualIteratedGadgetHomWeights
noncomputable section

def spaces : Code ⥤ SSet.{u} where
  obj := space
  map f := f.map

def rigidified : Code ⥤ SimplicialCat.{u, u} := spaces ⋙ rigidification

def source (P : Code) : (rigidified.{u}.obj P).Obj := RV (space P) (alpha P)
def target (P : Code) : (rigidified.{u}.obj P).Obj := RV (space P) (omega P)

theorem source_map {P Q : Code} (f : P ⟶ Q) :
    (rigidified.{u}.map f).obj (source P) = source Q :=
  (RigidificationVertices.vertexEquiv_naturality f.map (alpha P)).trans
    (congrArg (RV (space Q)) f.first)

theorem target_map {P Q : Code} (f : P ⟶ Q) :
    (rigidified.{u}.map f).obj (target P) = target Q :=
  (RigidificationVertices.vertexEquiv_naturality f.map (omega P)).trans
    (congrArg (RV (space Q)) f.last)

/-- Each weight is the unchanged original C(space P) Hom at the two actual endpoints. -/
def weights : Code ⥤ SSet.{u} where
  obj P := source P ⟶[SSet.{u}] target P
  map {P Q} f := castMap (rigidified.map f)
    (source P) (target P) (source Q) (target Q) (source_map f) (target_map f)
  map_id P := by
    rw [castMap_congr (rigidified.map_id P)
      (source P) (target P) (source P) (target P)
      (source_map (𝟙 P)) (target_map (𝟙 P)) rfl rfl]
    simp [castMap]
  map_comp {P Q R} f g :=
    (castMap_congr (rigidified.map_comp f g)
      (source P) (target P) (source R) (target R)
      (source_map (f ≫ g)) (target_map (f ≫ g))
      ((congrArg (rigidified.map g).obj (source_map f)).trans (source_map g))
      ((congrArg (rigidified.map g).obj (target_map f)).trans (target_map g))).trans
        (castMap_comp (rigidified.map f) (rigidified.map g)
          (source P) (target P) (source Q) (target Q) (source R) (target R)
          (source_map f) (target_map f) (source_map g) (target_map g))

/-- Contractibility is the already proved original endpoint-Hom result at every actual level. -/
theorem weights_point_GW (P : Code) : GW (pointMap (weights.{u}.obj P)) :=
  DaggerActualIteratedGadgetNecklaceComparison.point_GW_of_toUnit
    (DaggerActualIteratedGadgetProperties.endpoint_hom_GW P)

end
end DaggerActualIteratedGadgetHomWeights
