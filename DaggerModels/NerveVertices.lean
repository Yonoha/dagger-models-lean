import DaggerModels.OrdinaryRigidification
import DaggerModels.SimplicialObjectAdjunctions

/-!
# Actual degree-zero coherent-nerve vertices

Evaluation at the unique object of the original lifted zero thickening is an
equivalence with target objects. Its injectivity proves equality of full enriched
functors, including every simplex of every hom map. The original thickening,
path nerves, outer `ULift`, and arbitrary common universe are retained.
-/

open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerModels.OrdinaryRigidification.NerveVertices

noncomputable section

/-- The actual source of degree-zero simplices, with the original inner lift. -/
abbrev ZeroThickening := SimplicialThickening (ULift.{u} (Fin 1))

/-- The unique object of the actual zero thickening. -/
def zeroObject : ZeroThickening.{u} := .mk ⟨0⟩

theorem zeroObject_eq (i : ZeroThickening.{u}) : i = zeroObject := by
  cases i
  congr 1
  exact Subsingleton.elim _ _

/-- The underlying subset of every actual zero-dimensional path is a singleton. -/
theorem path_set_singleton (i j : ZeroThickening.{u}) (p : i ⟶ j) :
    p.I = {zeroObject.as} := by
  ext k
  constructor
  · intro _
    exact Subsingleton.elim _ _
  · intro _
    have h : k = i.as := Subsingleton.elim _ _
    rw [h]
    exact p.left

/-- All actual path objects agree, not merely their endpoints. -/
instance pathSubsingleton (i j : ZeroThickening.{u}) : Subsingleton (i ⟶ j) :=
  ⟨fun p q ↦ SimplicialThickening.Path.ext
    ((path_set_singleton i j p).trans (path_set_singleton i j q).symm)⟩

/-- Morphisms in the original induced path category retain its thinness. -/
instance pathIsThin (i j : ZeroThickening.{u}) : Quiver.IsThin (i ⟶ j) :=
  fun _ _ ↦ ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-- Every simplex in the original path nerve is the enriched identity simplex. -/
theorem hom_simplex_eq_identity (n : SimplexCategoryᵒᵖ)
    (p : (zeroObject.{u} ⟶[SSet.{u}] zeroObject).obj n) :
    p = (eId SSet zeroObject).app n PUnit.unit := by
  apply nerve.ext_of_isThin
  funext k
  exact Subsingleton.elim _ _

/-- The explicit terminal functor from the actual thickening to the existing discrete point. -/
def toDiscretePoint :
    SimplicialCat.of ZeroThickening.{u} ⟶ SimplicialCat.discrete.{u, u} PUnit.{u + 1} where
  obj _ := PUnit.unit
  map _ _ :=
    { app := fun _ _ ↦ ⟨⟨rfl⟩⟩
      naturality := by intros; rfl }
  map_id _ := by ext n p; rfl
  map_comp _ _ _ := by ext n p; rfl

/-- An object determines an actual enriched functor from the original zero thickening. -/
def vertexFunctor (C : SimplicialCat.{u, u}) (c : C.Obj) :
    EnrichedFunctor SSet.{u} ZeroThickening.{u} C.Obj :=
  toDiscretePoint ≫ SimplicialCat.discreteLift PUnit C (fun _ ↦ c)

theorem vertexFunctor_obj (C : SimplicialCat.{u, u}) (c : C.Obj)
    (i : ZeroThickening.{u}) : (vertexFunctor C c).obj i = c := rfl

/-- The inverse retains the full enriched identity map on every original hom simplex. -/
theorem vertexFunctor_map (C : SimplicialCat.{u, u}) (c : C.Obj)
    (i j : ZeroThickening.{u}) (n : SimplexCategoryᵒᵖ)
    (p : (i ⟶[SSet.{u}] j).obj n) :
    ((vertexFunctor C c).map i j).app n p = (eId SSet c).app n PUnit.unit := rfl

/-- Object evaluation determines the entire enriched functor, including all hom maps. -/
theorem functor_eq_vertexFunctor (C : SimplicialCat.{u, u})
    (F : EnrichedFunctor SSet.{u} ZeroThickening.{u} C.Obj) :
    F = vertexFunctor C (F.obj zeroObject) := by
  apply EnrichedFunctor.ext SSet (fun i ↦ by rw [zeroObject_eq i]; rfl)
  intro i j
  obtain rfl := zeroObject_eq i
  obtain rfl := zeroObject_eq j
  simp only [eqToHom_refl, Category.comp_id]
  ext n p
  rw [vertexFunctor_map, hom_simplex_eq_identity n p]
  exact congrArg (fun k ↦ k.app n PUnit.unit) (F.map_id zeroObject)

/-- Injectivity holds on actual enriched functors, not only on their object functions. -/
theorem evaluation_injective (C : SimplicialCat.{u, u}) :
    Function.Injective
      (fun F : EnrichedFunctor SSet.{u} ZeroThickening.{u} C.Obj ↦ F.obj zeroObject) := by
  intro F G h
  change F.obj zeroObject = G.obj zeroObject at h
  rw [functor_eq_vertexFunctor C F, functor_eq_vertexFunctor C G, h]

/-- The actual lifted degree-zero coherent nerve is equivalent to target objects. -/
def vertexEquiv (C : SimplicialCat.{u, u}) :
    (coherentNerve.obj C).obj (op ⦋0⦌) ≃ C.Obj where
  toFun P := P.down.obj zeroObject
  invFun c := ⟨vertexFunctor C c⟩
  left_inv P := by
    apply ULift.ext
    exact (functor_eq_vertexFunctor C P.down).symm
  right_inv _ := rfl

theorem vertexEquiv_apply (C : SimplicialCat.{u, u})
    (P : (coherentNerve.obj C).obj (op ⦋0⦌)) :
    vertexEquiv C P = P.down.obj zeroObject := rfl

theorem vertexEquiv_symm_down (C : SimplicialCat.{u, u}) (c : C.Obj) :
    ((vertexEquiv C).symm c).down = vertexFunctor C c := rfl

/-- Evaluation detects equality of actual lifted vertices and their complete functor data. -/
theorem vertex_ext (C : SimplicialCat.{u, u})
    {P Q : (coherentNerve.obj C).obj (op ⦋0⦌)}
    (h : P.down.obj zeroObject = Q.down.obj zeroObject) : P = Q :=
  (vertexEquiv C).injective h

/-- Evaluation is natural for every target enriched functor. -/
theorem vertexEquiv_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (P : (coherentNerve.obj C).obj (op ⦋0⦌)) :
    vertexEquiv D ((coherentNerve.map F).app (op ⦋0⦌) P) =
      F.obj (vertexEquiv C P) := rfl

/-- Naturality of the inverse is equality of full enriched functors. -/
theorem vertexFunctor_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (c : C.Obj) :
    EnrichedFunctor.comp SSet (vertexFunctor C c) F = vertexFunctor D (F.obj c) :=
  functor_eq_vertexFunctor D (EnrichedFunctor.comp SSet (vertexFunctor C c) F)

/-- The outer lifted inverse is natural under the actual nerve map. -/
theorem vertexEquiv_symm_naturality {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (c : C.Obj) :
    (coherentNerve.map F).app (op ⦋0⦌) ((vertexEquiv C).symm c) =
      (vertexEquiv D).symm (F.obj c) := by
  apply ULift.ext
  exact vertexFunctor_naturality F c

end

end DaggerModels.OrdinaryRigidification.NerveVertices
