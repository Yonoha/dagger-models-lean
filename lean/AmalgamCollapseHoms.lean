import AmalgamCollapse

/-! All original endpoint components and full functor laws of the same collapse. -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamPresentation

universe u

set_option autoImplicit false

namespace DaggerAmalgamCollapse

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

abbrev homOO (a d : C.Obj) :
    SimplicialCat.HomQuotient.hom (relations C.toSimplicialCat B.toSimplicialCat x b)
      (leftObj C.toSimplicialCat B.toSimplicialCat x b a)
      (leftObj C.toSimplicialCat B.toSimplicialCat x b d) ⟶ (a ⟶[SSet] d) :=
  (ordinary C B x b).map _ _

abbrev homON (a : C.Obj) (w : B.Obj) :
    SimplicialCat.HomQuotient.hom (relations C.toSimplicialCat B.toSimplicialCat x b)
      (leftObj C.toSimplicialCat B.toSimplicialCat x b a)
      (rightObj C.toSimplicialCat B.toSimplicialCat x b w) ⟶ (a ⟶[SSet] x) :=
  (ordinary C B x b).map _ _

abbrev homNO (z : B.Obj) (d : C.Obj) :
    SimplicialCat.HomQuotient.hom (relations C.toSimplicialCat B.toSimplicialCat x b)
      (rightObj C.toSimplicialCat B.toSimplicialCat x b z)
      (leftObj C.toSimplicialCat B.toSimplicialCat x b d) ⟶ (x ⟶[SSet] d) :=
  (ordinary C B x b).map _ _

abbrev homNN (z w : B.Obj) :
    SimplicialCat.HomQuotient.hom (relations C.toSimplicialCat B.toSimplicialCat x b)
      (rightObj C.toSimplicialCat B.toSimplicialCat x b z)
      (rightObj C.toSimplicialCat B.toSimplicialCat x b w) ⟶ (x ⟶[SSet] x) :=
  (ordinary C B x b).map _ _

theorem left_map_homOO (a d : C.Obj) :
    (leftLeg C.toSimplicialCat B.toSimplicialCat x b).map a d ≫
      homOO C B x b a d = 𝟙 _ := by
  ext q h
  exact ordinary_factor_left C B x b a d q h

theorem right_map_homNN (z w : B.Obj) :
    (rightLeg C.toSimplicialCat B.toSimplicialCat x b).map z w ≫
      homNN C B x b z w = toUnit (z ⟶[SSet] w) ≫ eId SSet x := by
  ext q h
  exact ordinary_factor_right C B x b z w q h

/-- Every supplied point, not only a chosen witness, collapses to the same unit. -/
theorem right_point_homNN (z w : B.Obj) (h : 𝟙_ SSet.{u} ⟶ (z ⟶[SSet] w)) :
    h ≫ (rightLeg C.toSimplicialCat B.toSimplicialCat x b).map z w ≫
      homNN C B x b z w = eId SSet x := by
  rw [right_map_homNN, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]

/-- This explicitly includes the original dagger of any supplied simplex. -/
theorem right_dagger_homNN (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (h : (z ⟶[SSet] w).obj q) :
    (homNN C B x b w z).app q
      ((rightLeg C.toSimplicialCat B.toSimplicialCat x b).map w z |>.app q
        ((B.daggerStructure.dagger z w).app q h)) =
      (eId SSet x).app q PUnit.unit :=
  ordinary_factor_right C B x b w z q ((B.daggerStructure.dagger z w).app q h)

variable (a d z : Objects C.toSimplicialCat B.toSimplicialCat x b)

theorem ordinary_nil (q : SimplexCategoryᵒᵖ) :
    ((ordinary C B x b).map a a).app q
      (SimplicialCat.HomQuotient.mk
        (relations C.toSimplicialCat B.toSimplicialCat x b) q .nil) =
      (eId SSet ((ordinary C B x b).obj a)).app q PUnit.unit :=
  congrFun (NatTrans.congr_app ((ordinary C B x b).map_id a) q) PUnit.unit

/-- Full same-operator naturality on the original quotient, including reductions. -/
theorem ordinary_naturality {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') :
    (SimplicialCat.HomQuotient.hom
      (relations C.toSimplicialCat B.toSimplicialCat x b) a z).map α ≫
      ((ordinary C B x b).map a z).app q' =
    ((ordinary C B x b).map a z).app q ≫
      ((ordinary C B x b).obj a ⟶[SSet] (ordinary C B x b).obj z).map α :=
  ((ordinary C B x b).map a z).naturality α

theorem ordinary_composition :
    (Q C.toSimplicialCat B.toSimplicialCat x b).enriched.comp a d z ≫
      (ordinary C B x b).map a z =
    ((ordinary C B x b).map a d ⊗ₘ (ordinary C B x b).map d z) ≫
      eComp SSet ((ordinary C B x b).obj a) ((ordinary C B x b).obj d)
        ((ordinary C B x b).obj z) :=
  (ordinary C B x b).map_comp a d z

theorem ordinary_dagger :
    (ordinary C B x b).map a z ≫
      C.daggerStructure.dagger ((ordinary C B x b).obj a) ((ordinary C B x b).obj z) =
    (Dagger.presentation C B x b).daggerStructure.dagger a z ≫
      (ordinary C B x b).map z a := by
  rw [← dagger_underlying C B x b]
  exact (dagger C B x b).map_dagger a z

end
end DaggerAmalgamCollapse
