import OriginalFlagFiberContractionPoint

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerOriginalFlagFlankification DaggerNerveHomotopy
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalFlagFiberContractionChecks

noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
variable (t : (flagHom X a b).obj (op ⦋n⦌))

theorem original_beta_data (p : Fiber X a b n t) :
    ((fiberToCenter X a b n t).app p).hom =
        ((fiberCenterIsTerminal X a b n t).from
          ((flankToFlankedFiber X a b n t).obj p)).hom.hom ∧
      ((fiberToCenter X a b n t).app p).hom.val.hom.map ≫
          (fiberCenterObj X a b n t).obj.1.map =
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.map ∧
      NecklaceCode.Flag.map ((fiberToCenter X a b n t).app p).hom.val.hom
          ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.2 =
        (fiberCenterObj X a b n t).obj.2 :=
  ⟨fiberToCenter_original_arrow X a b n t p,
    fiberToCenter_triangle X a b n t p, fiberToCenter_flag X a b n t p⟩

theorem original_center_class : classOf X a b n (fiberCenterObj X a b n t).obj = t :=
  fiberCenterObj_class X a b n t

theorem original_beta_endpoints (p : Fiber X a b n t) :
    ((fiberToCenter X a b n t).app p).hom.val.hom.map.app (op ⦋0⦌)
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.code.first =
      (fiberCenterObj X a b n t).obj.1.code.first ∧
    ((fiberToCenter X a b n t).app p).hom.val.hom.map.app (op ⦋0⦌)
        ((flankToFlankedFiber X a b n t ⋙ forgetFlankedFiber X a b n t).obj p).obj.1.code.last =
      (fiberCenterObj X a b n t).obj.1.code.last :=
  ⟨fiberToCenter_first X a b n t p, fiberToCenter_last X a b n t p⟩

theorem original_composition_isos :
    (fiberCollapseCenterIso X a b n t).hom ≫ (fiberCollapseCenterIso X a b n t).inv = 𝟙 _ ∧
      (fiberCollapseCenterIso X a b n t).inv ≫ (fiberCollapseCenterIso X a b n t).hom = 𝟙 _ ∧
      (fiberCenterCollapseIso X a b n t).hom ≫ (fiberCenterCollapseIso X a b n t).inv = 𝟙 _ ∧
      (fiberCenterCollapseIso X a b n t).inv ≫ (fiberCenterCollapseIso X a b n t).hom = 𝟙 _ :=
  ⟨(fiberCollapseCenterIso X a b n t).hom_inv_id,
    (fiberCollapseCenterIso X a b n t).inv_hom_id,
    (fiberCenterCollapseIso X a b n t).hom_inv_id,
    (fiberCenterCollapseIso X a b n t).inv_hom_id⟩

def original_both_R_homotopies :
    SSet.Homotopy (R.map (fiberCollapse X a b n t) ≫ R.map (fiberSection X a b n t))
        (𝟙 (R.obj (nerve (Fiber X a b n t)))) ×
      SSet.Homotopy (R.map (fiberSection X a b n t) ≫ R.map (fiberCollapse X a b n t))
        (𝟙 (R.obj (nerve fiberPointCat.{u}))) :=
  ⟨fiberHomInvId X a b n t, fiberInvHomId X a b n t⟩

theorem original_return_map :
    (fiberHomotopyEquiv X a b n t).homInvId.h =
      MonoidalClosed.uncurry
        ((SSet.Homotopy.equiv (fiberKappaRH X a b n t)).comp
          ((SSet.Homotopy.equiv (fiberBetaRH X a b n t)).inv.comp
            (SSet.Homotopy.equiv (fiberAlphaRH X a b n t)))).map := rfl

theorem original_delta_time (k : SimplexCategoryᵒᵖ)
    (x : (R.obj (nerve fiberPointCat.{u})).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (fiberHomotopyEquiv X a b n t).invHomId.h.app k (x, s) =
      (R.obj (nerve fiberPointCat.{u}) ◁ SSet.stdSimplex.toSSetObjI ≫
        (Functor.Monoidal.μIso TopCat.toSSet
          (SSet.toTop.obj (nerve fiberPointCat.{u})) TopCat.I).hom ≫
            TopCat.toSSet.map
              ((SSet.stdSimplex.toTopTensorDeltaOneIso (nerve fiberPointCat.{u})).inv ≫
                SSet.toTop.map
                  (natTransMap (fiberCenterCollapseIso X a b n t).hom))).app k (x, s) :=
  fiberInvHomId_time X a b n t k x s

theorem original_point_inverse_laws :
    fiberPointNerveIsoDelta0.hom ≫ fiberPointNerveIsoDelta0.inv =
        𝟙 (nerve fiberPointCat.{u}) ∧
      fiberPointNerveIsoDelta0.inv ≫ fiberPointNerveIsoDelta0.hom = 𝟙 (Δ[0] : SSet.{u}) :=
  ⟨fiberPointNerveIsoDelta0_hom_inv, fiberPointNerveIsoDelta0_inv_hom⟩

theorem original_collapse_and_W :
    fiberCollapseDelta0 X a b n t =
        SSet.stdSimplex.isTerminalObj₀.from (nerve (Fiber X a b n t)) ∧
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapse X a b n t))) ∧
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapseDelta0 X a b n t))) :=
  ⟨fiberCollapseDelta0_triangle X a b n t,
    fiber_collapse_geometric X a b n t, fiber_delta0_collapse_geometric X a b n t⟩

theorem original_universe0_diagonal (Y : SSet.{0}) (x : Y.obj (op ⦋0⦌))
    (s : (flagHom Y x x).obj (op ⦋0⦌)) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapseDelta0 Y x x 0 s))) :=
  fiber_delta0_collapse_geometric Y x x 0 s

end

end DaggerOriginalFlagFiberContractionChecks
