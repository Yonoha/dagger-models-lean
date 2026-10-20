import ActualQQuillenEquivalence
import ActualGeneralRightConeNaturality

/-! Actual original rigidification Hom evaluation of EVERY whole right-cone simplex in ANY X. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerModels OrdinaryRigidification
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerActualGeneralRightConeMapping
universe u
namespace DaggerActualGeneralRightConeRigidificationLeg
noncomputable section
private abbrev RV := RigidificationVertices.vertexEquiv.{u}

def originalHom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : SSet.{u} :=
  (rigidification.obj X).enriched.Hom (RV X a) (RV X b)

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

theorem leg_source (q : SimplexCategory) (σ : (rightMapping X a b).obj (op q)) :
    (rigidification.map σ.val).obj (alphaObj q.len) = RV X a :=
  (RigidificationVertices.vertexEquiv_naturality σ.val (alpha q.len)).trans
    (congrArg (RV X) σ.property.1)

theorem leg_target (q : SimplexCategory) (σ : (rightMapping X a b).obj (op q)) :
    (rigidification.map σ.val).obj (omegaObj q.len) = RV X b :=
  (RigidificationVertices.vertexEquiv_naturality σ.val (omega q.len)).trans
    (congrArg (RV X) σ.property.2)

def leg (q : SimplexCategory) (σ : (rightMapping X a b).obj (op q)) :
    Q q.len ⟶ originalHom X a b :=
  castMap (rigidification.map σ.val) (alphaObj q.len) (omegaObj q.len)
    (RV X a) (RV X b) (leg_source X a b q σ) (leg_target X a b q σ)

theorem leg_formula (q : SimplexCategory) (σ : (rightMapping X a b).obj (op q)) :
    leg X a b q σ = (rigidification.map σ.val).map (alphaObj q.len) (omegaObj q.len) ≫
      OriginalOrdinaryEndpointTransport.transport (rigidification.obj X)
        (leg_source X a b q σ) (leg_target X a b q σ) := rfl

theorem leg_precomp {m n : SimplexCategory} (α : m ⟶ n)
    (σ : (rightMapping X a b).obj (op n)) :
    leg X a b m ((rightMapping X a b).map α.op σ) =
      QFunctor.map α ≫ leg X a b n σ := by
  unfold leg
  change castMap (rigidification.map (coneMap α ≫ σ.val))
      (alphaObj m.len) (omegaObj m.len) (RV X a) (RV X b) _ _ = _
  exact (castMap_congr (rigidification.map_comp (coneMap α) σ.val)
    (alphaObj m.len) (omegaObj m.len) (RV X a) (RV X b) _ _
    ((congrArg (rigidification.map σ.val).obj (sourceObject_map α)).trans
      (leg_source X a b n σ))
    ((congrArg (rigidification.map σ.val).obj (targetObject_map α)).trans
      (leg_target X a b n σ))).trans
    (castMap_comp (rigidification.map (coneMap α)) (rigidification.map σ.val)
      (alphaObj m.len) (omegaObj m.len) (alphaObj n.len) (omegaObj n.len)
      (RV X a) (RV X b) (sourceObject_map α) (targetObject_map α)
      (leg_source X a b n σ) (leg_target X a b n σ))

def homMap {Y : SSet.{u}} (f : X ⟶ Y) :
    originalHom X a b ⟶ originalHom Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) :=
  castMap (rigidification.map f) (RV X a) (RV X b)
    (RV Y (f.app (op ⦋0⦌) a)) (RV Y (f.app (op ⦋0⦌) b))
    (RigidificationVertices.vertexEquiv_naturality f a)
    (RigidificationVertices.vertexEquiv_naturality f b)

theorem leg_postcomp {Y : SSet.{u}} (f : X ⟶ Y) (q : SimplexCategory)
    (σ : (rightMapping X a b).obj (op q)) :
    leg Y (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) q
        ((DaggerActualGeneralRightConeMapping.map f a b).app (op q) σ) =
      leg X a b q σ ≫ homMap X a b f := by
  unfold leg homMap
  rw [← castMap_comp]
  exact castMap_congr (rigidification.map_comp σ.val f)
    (alphaObj q.len) (omegaObj q.len)
    (RV Y (f.app (op ⦋0⦌) a)) (RV Y (f.app (op ⦋0⦌) b)) _ _ _ _

end
end DaggerActualGeneralRightConeRigidificationLeg
