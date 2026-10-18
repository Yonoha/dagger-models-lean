import AmalgamEvaluation
import AmalgamCollapseHoms

/-! The accepted original collapse evaluated on the exact low-rank raw paths.
All endpoint transports, original composition maps and empty Fin factors are retained. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamPresentation DaggerAmalgamPaddedClassification
open DaggerAmalgamUnitBoundary DaggerAmalgamCollapse

universe u

set_option autoImplicit false

namespace DaggerAmalgamSuccessor

noncomputable section

variable (C B : DaggerSimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- Equality elimination preserves the same collapsed path at transported endpoints. -/
theorem ordinary_castPath {q : SimplexCategoryᵒᵖ}
    {s t s' t' : Objects C.toSimplicialCat B.toSimplicialCat x b}
    (hs : s = s') (ht : t = t')
    (p : Path C.toSimplicialCat B.toSimplicialCat x b q s t) :
    ((ordinary C B x b).map s' t').app q
      (SimplicialCat.HomQuotient.mk _ q
        (castPath C.toSimplicialCat B.toSimplicialCat x b hs ht p)) =
      cast (by cases hs; cases ht; rfl)
        (((ordinary C B x b).map s t).app q (SimplicialCat.HomQuotient.mk _ q p)) := by
  cases hs
  cases ht
  rfl

theorem ordinary_bLoop (q : SimplexCategoryᵒᵖ) (h : (b ⟶[SSet] b).obj q) :
    ((ordinary C B x b).map _ _).app q
      (SimplicialCat.HomQuotient.mk _ q
        (bLoop C.toSimplicialCat B.toSimplicialCat x b q h)) =
      (eId SSet x).app q PUnit.unit := by
  rw [bLoop, ordinary_castPath]
  exact ordinary_factor_right C B x b b b q h

theorem ordinary_bStart (q : SimplexCategoryᵒᵖ) (z : B.Obj)
    (h : (z ⟶[SSet] b).obj q) :
    ((ordinary C B x b).map _ _).app q
      (SimplicialCat.HomQuotient.mk _ q
        (bStart C.toSimplicialCat B.toSimplicialCat x b q h)) =
      (eId SSet x).app q PUnit.unit := by
  rw [bStart, ordinary_castPath]
  exact ordinary_factor_right C B x b z b q h

theorem ordinary_bEnd (q : SimplexCategoryᵒᵖ) (w : B.Obj)
    (h : (b ⟶[SSet] w).obj q) :
    ((ordinary C B x b).map _ _).app q
      (SimplicialCat.HomQuotient.mk _ q
        (bEnd C.toSimplicialCat B.toSimplicialCat x b q h)) =
      (eId SSet x).app q PUnit.unit := by
  rw [bEnd, ordinary_castPath]
  exact ordinary_factor_right C B x b b w q h

/-- Composition is the existing quotient functor's original enriched composition law. -/
theorem ordinary_path_comp (q : SimplexCategoryᵒᵖ)
    {s t v : Objects C.toSimplicialCat B.toSimplicialCat x b}
    (p : Path C.toSimplicialCat B.toSimplicialCat x b q s t)
    (r : Path C.toSimplicialCat B.toSimplicialCat x b q t v) :
    ((ordinary C B x b).map s v).app q
      (SimplicialCat.HomQuotient.mk _ q (p.comp r)) =
      (eComp SSet ((ordinary C B x b).obj s) ((ordinary C B x b).obj t)
        ((ordinary C B x b).obj v)).app q
          (((ordinary C B x b).map s t).app q (SimplicialCat.HomQuotient.mk _ q p),
            ((ordinary C B x b).map t v).app q (SimplicialCat.HomQuotient.mk _ q r)) :=
  congrFun (NatTrans.congr_app (ordinary_composition C B x b s t v) q)
    (SimplicialCat.HomQuotient.mk _ q p, SimplicialCat.HomQuotient.mk _ q r)

theorem unit_comp_app (a d : C.Obj) (q : SimplexCategoryᵒᵖ)
    (h : (a ⟶[SSet] d).obj q) :
    (eComp SSet a a d).app q ((eId SSet a).app q PUnit.unit, h) = h :=
  congrArg (fun f ↦ f.app q h) (e_id_comp SSet a d)

theorem comp_unit_app (a d : C.Obj) (q : SimplexCategoryᵒᵖ)
    (h : (a ⟶[SSet] d).obj q) :
    (eComp SSet a d d).app q (h, (eId SSet d).app q PUnit.unit) = h :=
  congrArg (fun f ↦ f.app q h) (e_comp_id SSet a d)

theorem ordinary_decodeON_zero (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj)
    (h : RawON C.toSimplicialCat B.toSimplicialCat x b q a w 0) :
    ((ordinary C B x b).map _ _).app q (SimplicialCat.HomQuotient.mk _ q
      (decodeON C.toSimplicialCat B.toSimplicialCat x b q a w 0 h)) = h.1 := by
  dsimp only [decodeON, zig]
  erw [ordinary_path_comp, ordinary_path_comp,
    ordinary_factor_left C B x b a x q h.1,
    ordinary_nil C B x b (leftObj C.toSimplicialCat B.toSimplicialCat x b x) q,
    ordinary_bEnd C B x b q w h.2.2.2]
  change (eComp SSet a x x).app q
    ((eComp SSet a x x).app q (h.1, (eId SSet x).app q PUnit.unit),
      (eId SSet x).app q PUnit.unit) = h.1
  rw [comp_unit_app, comp_unit_app]

theorem ordinary_decodeNO_zero (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj)
    (h : RawNO C.toSimplicialCat B.toSimplicialCat x b q z d 0) :
    ((ordinary C B x b).map _ _).app q (SimplicialCat.HomQuotient.mk _ q
      (decodeNO C.toSimplicialCat B.toSimplicialCat x b q z d 0 h)) = h.2.2.2 := by
  dsimp only [decodeNO, zag]
  erw [ordinary_path_comp, ordinary_path_comp, ordinary_bStart C B x b q z h.1,
    ordinary_nil C B x b (leftObj C.toSimplicialCat B.toSimplicialCat x b x) q,
    ordinary_factor_left C B x b x d q h.2.2.2]
  change (eComp SSet x x d).app q
    ((eComp SSet x x x).app q
      ((eId SSet x).app q PUnit.unit, (eId SSet x).app q PUnit.unit), h.2.2.2) = h.2.2.2
  rw [comp_unit_app, unit_comp_app]

/-- The original exceptional NN1 comparison is exactly the middle C-loop coordinate. -/
theorem ordinary_decodeNN_one (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (h : RawNN C.toSimplicialCat B.toSimplicialCat x b q z w 1) :
    ((ordinary C B x b).map _ _).app q (SimplicialCat.HomQuotient.mk _ q
      (decodeNN C.toSimplicialCat B.toSimplicialCat x b q z w 1 h)) = h.2.1 0 := by
  dsimp only [decodeNN, zag]
  erw [ordinary_path_comp, ordinary_path_comp, ordinary_path_comp,
    ordinary_bStart C B x b q z h.1,
    ordinary_nil C B x b (leftObj C.toSimplicialCat B.toSimplicialCat x b x) q,
    ordinary_factor_left C B x b x x q (h.2.1 (Fin.last 0)),
    ordinary_bEnd C B x b q w h.2.2.2]
  change (eComp SSet x x x).app q
    ((eComp SSet x x x).app q
      ((eComp SSet x x x).app q
        ((eId SSet x).app q PUnit.unit, (eId SSet x).app q PUnit.unit),
          h.2.1 (Fin.last 0)), (eId SSet x).app q PUnit.unit) = h.2.1 0
  simp only [comp_unit_app, unit_comp_app]
  rfl

theorem evaluationOO_zero_collapse (a d : C.Obj) :
    evaluationOO C.toSimplicialCat B.toSimplicialCat x b a d 0 ≫ homOO C B x b a d =
      𝟙 (a ⟶[SSet] d) := by
  rw [evaluationOO_zero, left_map_homOO]

theorem evaluationNN_zero_collapse (z w : B.Obj) :
    evaluationNN C.toSimplicialCat B.toSimplicialCat x b z w 0 ≫ homNN C B x b z w =
      toUnit (z ⟶[SSet] w) ≫ eId SSet x := by
  rw [evaluationNN_zero, right_map_homNN]

end
end DaggerAmalgamSuccessor
