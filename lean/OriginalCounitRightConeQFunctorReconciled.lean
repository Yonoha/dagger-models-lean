import OriginalCounitRightConeFunctor
import OriginalOrdinaryMovingHomDiagramReconciled

/-!
# The actual right-cone Hom simplicial sets form a cosimplicial diagram

The object in degree `n` is the original `Q n`, the enriched Hom between
the two distinct formal endpoints of the original pushout cone. Both
endpoint equalities are retained in every transition map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor

universe u

namespace DaggerOriginalCounitRightConeQFunctor

noncomputable section

private abbrev C := OrdinaryRigidification.rigidification.{u}

/-- Evaluating the natural formal left endpoint at the unique zero-simplex. -/
theorem alpha_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (coneMap.{u} f).app (op ⦋0⦌) (alpha.{u} m.len) = alpha.{u} n.len := by
  have h := congrArg
    (fun g : (Δ[0] : SSet.{u}) ⟶ cone.{u} n.len ↦
      g.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    (alphaMap_naturality.{u} f)
  simpa only [alpha, NatTrans.comp_app, types_comp_apply] using h

/-- Evaluating the natural formal right endpoint at the unique zero-simplex. -/
theorem omega_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    (coneMap.{u} f).app (op ⦋0⦌) (omega.{u} m.len) = omega.{u} n.len := by
  have h := congrArg
    (fun g : (Δ[0] : SSet.{u}) ⟶ cone.{u} n.len ↦
      g.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    (omegaMap_naturality.{u} f)
  simpa only [omega, NatTrans.comp_app, types_comp_apply] using h

/-- The same original rigidification, applied to the actual cone functor. -/
def rigidifiedCones : SimplexCategory ⥤ SimplicialCat.{u, u} :=
  coneFunctor.{u} ⋙ C

/-- The original left endpoint in each rigidified cone. -/
def sourceObject (m : SimplexCategory) : (rigidifiedCones.{u}.obj m).Obj :=
  alphaObj.{u} m.len

/-- The original right endpoint in each rigidified cone. -/
def targetObject (m : SimplexCategory) : (rigidifiedCones.{u}.obj m).Obj :=
  omegaObj.{u} m.len

/-- The left endpoint is natural under the actual rigidified cone map. -/
theorem sourceObject_map {m n : SimplexCategory} (f : m ⟶ n) :
    (rigidifiedCones.{u}.map f).obj (sourceObject.{u} m) = sourceObject.{u} n := by
  change (C.map (coneMap.{u} f)).obj (alphaObj.{u} m.len) = alphaObj.{u} n.len
  rw [alphaObj, RigidificationVertices.vertexEquiv_naturality
    (coneMap.{u} f) (alpha.{u} m.len), alpha_naturality]
  rfl

/-- The right endpoint is natural under the actual rigidified cone map. -/
theorem targetObject_map {m n : SimplexCategory} (f : m ⟶ n) :
    (rigidifiedCones.{u}.map f).obj (targetObject.{u} m) = targetObject.{u} n := by
  change (C.map (coneMap.{u} f)).obj (omegaObj.{u} m.len) = omegaObj.{u} n.len
  rw [omegaObj, RigidificationVertices.vertexEquiv_naturality
    (coneMap.{u} f) (omega.{u} m.len), omega_naturality]
  rfl

/-- The actual enriched Hom map, with both endpoint transports. -/
def Qmap {m n : SimplexCategory} (f : m ⟶ n) :
    Q.{u} m.len ⟶ Q.{u} n.len :=
  castMap (rigidifiedCones.{u}.map f)
    (sourceObject.{u} m) (targetObject.{u} m)
    (sourceObject.{u} n) (targetObject.{u} n)
    (sourceObject_map.{u} f) (targetObject_map.{u} f)

/-- Formula for the original Hom map followed by its two endpoint casts. -/
theorem Qmap_formula {m n : SimplexCategory} (f : m ⟶ n) :
    Qmap.{u} f =
      (C.map (coneMap.{u} f)).map (alphaObj.{u} m.len) (omegaObj.{u} m.len) ≫
        OriginalOrdinaryEndpointTransport.transport (C.obj (cone.{u} n.len))
          (sourceObject_map.{u} f) (targetObject_map.{u} f) := rfl

/-- The same original `Q n` assembles into a cosimplicial simplicial set. -/
def QFunctor : SimplexCategory ⥤ SSet.{u} where
  obj m := Q.{u} m.len
  map f := Qmap.{u} f
  map_id m := by
    change castMap (rigidifiedCones.{u}.map (𝟙 m))
      (sourceObject.{u} m) (targetObject.{u} m)
      (sourceObject.{u} m) (targetObject.{u} m)
      (sourceObject_map.{u} (𝟙 m)) (targetObject_map.{u} (𝟙 m)) = _
    rw [castMap_congr (rigidifiedCones.{u}.map_id m)
      (sourceObject.{u} m) (targetObject.{u} m)
      (sourceObject.{u} m) (targetObject.{u} m)
      (sourceObject_map.{u} (𝟙 m)) (targetObject_map.{u} (𝟙 m)) rfl rfl]
    simp [castMap]
    rfl
  map_comp {m n p} f g := by
    exact (castMap_congr (rigidifiedCones.{u}.map_comp f g)
      (sourceObject.{u} m) (targetObject.{u} m)
      (sourceObject.{u} p) (targetObject.{u} p)
      (sourceObject_map.{u} (f ≫ g)) (targetObject_map.{u} (f ≫ g))
      ((congrArg (rigidifiedCones.{u}.map g).obj
        (sourceObject_map.{u} f)).trans (sourceObject_map.{u} g))
      ((congrArg (rigidifiedCones.{u}.map g).obj
        (targetObject_map.{u} f)).trans (targetObject_map.{u} g))).trans
        (castMap_comp (rigidifiedCones.{u}.map f) (rigidifiedCones.{u}.map g)
          (sourceObject.{u} m) (targetObject.{u} m)
          (sourceObject.{u} n) (targetObject.{u} n)
          (sourceObject.{u} p) (targetObject.{u} p)
          (sourceObject_map.{u} f) (targetObject_map.{u} f)
          (sourceObject_map.{u} g) (targetObject_map.{u} g))

/-- The literal object of the diagram is the previously chosen `Q n`. -/
theorem QFunctor_obj (m : SimplexCategory) :
    QFunctor.{u}.obj m = Q.{u} m.len := rfl

/-- The literal transition is the original map with both endpoint casts. -/
theorem QFunctor_map {m n : SimplexCategory} (f : m ⟶ n) :
    QFunctor.{u}.map f = Qmap.{u} f := rfl

/-- The constant diagram at the terminal standard zero-simplex. -/
def pointFunctor : SimplexCategory ⥤ SSet.{u} :=
  (Functor.const SimplexCategory).obj (Δ[0] : SSet.{u})

/-- The canonical point augmentation of the actual `Q` diagram. -/
def augmentation : QFunctor.{u} ⟶ pointFunctor.{u} where
  app m := SSet.stdSimplex.isTerminalObj₀.from (QFunctor.{u}.obj m)
  naturality _ _ _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end

end DaggerOriginalCounitRightConeQFunctor
