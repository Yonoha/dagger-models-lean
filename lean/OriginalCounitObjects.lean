import DaggerModels.RigidificationVertices
import DaggerModels.DaggerAdjunction

set_option autoImplicit false

open CategoryTheory Opposite DaggerModels
open scoped Simplicial

universe u

namespace DaggerOriginalCounitObjects

noncomputable section

open OrdinaryRigidification

abbrev C : SSet.{u} ⥤ SimplicialCat.{u, u} := rigidification
abbrev N : SimplicialCat.{u, u} ⥤ SSet.{u} := coherentNerve
abbrev A : C.{u} ⊣ N.{u} := rigidificationCoherentNerveAdjunction

private abbrev RV (X : SSet.{u}) := RigidificationVertices.vertexEquiv X
private abbrev NV (D : SimplicialCat.{u, u}) := NerveVertices.vertexEquiv D

/-- The original counit carries the object of a vertex to its nerve value. -/
theorem counit_obj_vertex (D : SimplicialCat.{u, u})
    (v : (N.obj D).obj (op ⦋0⦌)) :
    (A.counit.app D).obj (RV (N.obj D) v) = NV D v := by
  let ε : C.obj (N.obj D) ⟶ D := A.counit.app D
  let η : N.obj D ⟶ N.obj (C.obj (N.obj D)) := A.unit.app (N.obj D)
  have htriangle : η ≫ N.map ε = 𝟙 (N.obj D) := A.right_triangle_components D
  have hv : (N.map ε).app (op ⦋0⦌) (η.app (op ⦋0⦌) v) = v := by
    have h := congrFun (NatTrans.congr_app htriangle (op ⦋0⦌)) v
    simpa using h
  calc
    ε.obj (RV (N.obj D) v) =
        ε.obj (NV (C.obj (N.obj D)) (η.app (op ⦋0⦌) v)) := by
          rfl
    _ = NV D ((N.map ε).app (op ⦋0⦌) (η.app (op ⦋0⦌) v)) :=
      (NerveVertices.vertexEquiv_naturality ε _).symm
    _ = NV D v := congrArg (NV D) hv

/-- The actual counit object function is surjective, without a Kan premise. -/
theorem counit_obj_surjective (D : SimplicialCat.{u, u}) :
    Function.Surjective (A.counit.app D).obj := by
  intro d
  obtain ⟨v, rfl⟩ := (NV D).surjective d
  exact ⟨RV (N.obj D) v, counit_obj_vertex D v⟩

/-- Both original vertex equivalences make the counit object function injective. -/
theorem counit_obj_injective (D : SimplicialCat.{u, u}) :
    Function.Injective (A.counit.app D).obj := by
  intro a b h
  obtain ⟨v, rfl⟩ := (RV (N.obj D)).surjective a
  obtain ⟨w, rfl⟩ := (RV (N.obj D)).surjective b
  apply congrArg (RV (N.obj D))
  apply (NV D).injective
  calc
    NV D v = (A.counit.app D).obj (RV (N.obj D) v) :=
      (counit_obj_vertex D v).symm
    _ = (A.counit.app D).obj (RV (N.obj D) w) := h
    _ = NV D w := counit_obj_vertex D w

theorem counit_obj_bijective (D : SimplicialCat.{u, u}) :
    Function.Bijective (A.counit.app D).obj :=
  ⟨counit_obj_injective D, counit_obj_surjective D⟩

/-- Forgetting the dagger identifies this very counit with the original ordinary counit. -/
theorem dagger_counit_obj_bijective (D : DaggerSimplicialCat.{u, u}) :
    Function.Bijective
      (DaggerAdjunction.daggerRigidificationCoherentNerveAdjunction.counit.app D).obj := by
  let e := DaggerAdjunction.daggerRigidificationCoherentNerveAdjunction.counit.app D
  change Function.Bijective e.toEnrichedFunctor.obj
  dsimp only [e]
  rw [DaggerAdjunction.adjunction_counit D]
  exact counit_obj_bijective D.toSimplicialCat

end

end DaggerOriginalCounitObjects
