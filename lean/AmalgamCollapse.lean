import AmalgamPresentation

/-! The actual collapse induced by the identity and the original terminal point.
No weak-equivalence or classifier hypothesis is used in this construction. -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamPresentation

universe u

set_option autoImplicit false

namespace DaggerAmalgamCollapse

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- Reuse the existing actual terminal point and original object selector. -/
def constant : B ⟶ C :=
  DaggerDiscreteObjects.toPoint B ≫ DaggerDiscreteObjects.fromPoint C x

theorem constant_obj (z : B.Obj) : (constant C B x).obj z = x := rfl

theorem constant_map (z w : B.Obj) :
    (constant C B x).map z w = toUnit (z ⟶[SSet] w) ≫ eId SSet x := by
  ext q h
  rfl

theorem constant_map_app (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (h : (z ⟶[SSet] w).obj q) :
    ((constant C B x).map z w).app q h = (eId SSet x).app q PUnit.unit := rfl

theorem point_condition : DaggerDiscreteObjects.fromPoint C x ≫ 𝟙 C =
    DaggerDiscreteObjects.fromPoint B b ≫ constant C B x := by
  apply (DaggerDiscreteObjects.pointHomEquiv C).injective
  rfl

/-- The full original ordinary factor functors with their literal glued object. -/
def ordinaryData : Data C.toSimplicialCat B.toSimplicialCat x b C.toSimplicialCat :=
  ⟨(fun c ↦ match c with
    | false => 𝟙 C.toSimplicialCat
    | true => DaggerSimplicialCat.forget.map (constant C B x)), rfl⟩

def ordinary : Q C.toSimplicialCat B.toSimplicialCat x b ⟶ C.toSimplicialCat :=
  desc C.toSimplicialCat B.toSimplicialCat x b (ordinaryData C B x b)

theorem ordinary_left : leftLeg C.toSimplicialCat B.toSimplicialCat x b ≫
    ordinary C B x b = 𝟙 C.toSimplicialCat :=
  leg_desc C.toSimplicialCat B.toSimplicialCat x b (ordinaryData C B x b) false

theorem ordinary_right : rightLeg C.toSimplicialCat B.toSimplicialCat x b ≫
    ordinary C B x b = DaggerSimplicialCat.forget.map (constant C B x) :=
  leg_desc C.toSimplicialCat B.toSimplicialCat x b (ordinaryData C B x b) true

theorem ordinary_obj_left (a : C.Obj) :
    (ordinary C B x b).obj (leftObj C.toSimplicialCat B.toSimplicialCat x b a) = a := rfl

theorem ordinary_obj_right (z : B.Obj) :
    (ordinary C B x b).obj (rightObj C.toSimplicialCat B.toSimplicialCat x b z) = x := rfl

theorem ordinary_factor_left (a d : C.Obj) (q : SimplexCategoryᵒᵖ)
    (h : (a ⟶[SSet] d).obj q) :
    ((ordinary C B x b).map _ _).app q
      (SimplicialCat.HomQuotient.mk _ q
        (factorPath C.toSimplicialCat B.toSimplicialCat x b false q h)) = h :=
  freeExtension_factor C.toSimplicialCat B.toSimplicialCat x b
    (ordinaryData C B x b) false q h

theorem ordinary_factor_right (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (h : (z ⟶[SSet] w).obj q) :
    ((ordinary C B x b).map _ _).app q
      (SimplicialCat.HomQuotient.mk _ q
        (factorPath C.toSimplicialCat B.toSimplicialCat x b true q h)) =
      (eId SSet x).app q PUnit.unit :=
  freeExtension_factor C.toSimplicialCat B.toSimplicialCat x b
    (ordinaryData C B x b) true q h

/-- The same construction through the full dagger pushout universal property. -/
def dagger : Dagger.presentation C B x b ⟶ C :=
  Dagger.desc C B x b (𝟙 C) (constant C B x) (point_condition C B x b)

theorem dagger_left : Dagger.left C B x b ≫ dagger C B x b = 𝟙 C :=
  Dagger.left_desc C B x b (𝟙 C) (constant C B x) (point_condition C B x b)

theorem dagger_right : Dagger.right C B x b ≫ dagger C B x b = constant C B x :=
  Dagger.right_desc C B x b (𝟙 C) (constant C B x) (point_condition C B x b)

theorem dagger_underlying : DaggerSimplicialCat.forget.map (dagger C B x b) =
    ordinary C B x b := by
  apply desc_unique C.toSimplicialCat B.toSimplicialCat x b (ordinaryData C B x b)
  intro c
  cases c
  · have h := congrArg DaggerSimplicialCat.forget.map (dagger_left C B x b)
    simpa only [Functor.map_comp, Dagger.left_underlying, Functor.map_id] using h
  · have h := congrArg DaggerSimplicialCat.forget.map (dagger_right C B x b)
    simpa only [Functor.map_comp, Dagger.right_underlying] using h

variable {P : DaggerSimplicialCat.{u, u}} (i : C ⟶ P) (j : B ⟶ P)
  (sq : IsPushout (DaggerDiscreteObjects.fromPoint C x)
    (DaggerDiscreteObjects.fromPoint B b) i j)

/-- Transfer through the accepted whole original-apex isomorphism. -/
def original : P ⟶ C :=
  (Dagger.originalIso C B x b i j sq).inv ≫ dagger C B x b

theorem original_left : i ≫ original C B x b i j sq = 𝟙 C := by
  rw [original, ← Category.assoc, Dagger.left_originalIso_inv, dagger_left]

theorem original_right : j ≫ original C B x b i j sq = constant C B x := by
  rw [original, ← Category.assoc, Dagger.right_originalIso_inv, dagger_right]

theorem original_unique (F : P ⟶ C) (hC : i ≫ F = 𝟙 C)
    (hB : j ≫ F = constant C B x) : F = original C B x b i j sq := by
  apply sq.hom_ext
  · exact hC.trans (original_left C B x b i j sq).symm
  · exact hB.trans (original_right C B x b i j sq).symm

end
end DaggerAmalgamCollapse
