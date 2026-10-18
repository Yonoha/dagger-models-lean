import ChosenEnrichedMapTransport
import SSetProductGeometric

set_option autoImplicit false

open CategoryTheory EnrichedCategory HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerSSetProductGeometric
open scoped SSet.modelCategoryQuillen

universe o u

namespace DaggerOriginalEnrichedHomTransport

noncomputable section

variable {A B : DaggerModels.SimplicialCat.{o,u}}

/-- The original object function of an enriched functor respects whole-functor equality. -/
theorem functorObjEq {F G : A ⟶ B} (h : F = G) (x : A.Obj) :
    F.obj x = G.obj x :=
  congrArg (fun K : A ⟶ B ↦ K.obj x) h

/-- The same original Hom map, including transports of both object endpoints. -/
theorem functorHomEq {F G : A ⟶ B} (h : F = G) (x y : A.Obj) :
    F.map x y ≫ targetHomTransport (functorObjEq h x) (functorObjEq h y) =
      G.map x y :=
  enrichedFunctor_hom_congr h x y (functorObjEq h x) (functorObjEq h y)

/-- Transport along both original object equalities is an isomorphism. -/
theorem homTransport_isIso {a b c d : B.Obj} (ha : a = c) (hb : b = d) :
    IsIso (targetHomTransport ha hb) := by
  unfold targetHomTransport
  infer_instance

/-- Geometric weak equivalence is unaffected by the two actual endpoint casts. -/
theorem GW_transport_iff {a b c d : B.Obj} {K : SSet.{u}}
    (ha : a = c) (hb : b = d) (f : K ⟶ (a ⟶[SSet.{u}] b)) :
    GW (f ≫ targetHomTransport ha hb) ↔ GW f := by
  cases ha
  cases hb
  simp only [targetHomTransport, eqToHom_refl, Category.comp_id]

/-- Whole enriched-functor equality transports the exact original Hom-W assertion. -/
theorem GW_functorHom_congr {F G : A ⟶ B} (h : F = G) (x y : A.Obj) :
    GW (F.map x y) ↔ GW (G.map x y) := by
  rw [← functorHomEq h x y]
  exact (GW_transport_iff (functorObjEq h x) (functorObjEq h y) (F.map x y)).symm

end

end DaggerOriginalEnrichedHomTransport
