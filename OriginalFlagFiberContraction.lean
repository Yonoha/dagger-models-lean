import OriginalFlagFiberContractionData
import NerveHomotopy

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed

universe u v

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode DaggerNerveHomotopy

section FormulaWrappers

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {A B : C ⥤ D} (zeta : A ⟶ B)

/-- One wrapper for all supplied NTs, with the actual complete time chain. -/
theorem nerveNT_time_formula (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve C).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (natTransHomotopy zeta).h.app k (gamma, s) =
      ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.prod' gamma) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁ zeta) := rfl

theorem nerveNT_time_obj (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve C).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k)
    (i : Fin (k.unop.len + 1)) :
    ((natTransHomotopy zeta).h.app k (gamma, s)).obj i =
      ((ComposableArrows.mk₁ zeta).obj
        ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.obj i)).obj
          (gamma.obj i) := rfl

theorem nerveNT_time_obj_zero (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve C).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k)
    (i : Fin (k.unop.len + 1))
    (hs : (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.obj i = (0 : Fin 2)) :
    ((natTransHomotopy zeta).h.app k (gamma, s)).obj i = A.obj (gamma.obj i) := by
  rw [nerveNT_time_obj, hs]
  rfl

theorem nerveNT_time_obj_one (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve C).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k)
    (i : Fin (k.unop.len + 1))
    (hs : (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.obj i = (1 : Fin 2)) :
    ((natTransHomotopy zeta).h.app k (gamma, s)).obj i = B.obj (gamma.obj i) := by
  rw [nerveNT_time_obj, hs]
  rfl

theorem nerveNT_time_map (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve C).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k)
    {i j : Fin (k.unop.len + 1)} (f : i ⟶ j) :
    ((natTransHomotopy zeta).h.app k (gamma, s)).map f =
      ((ComposableArrows.mk₁ zeta).map
        ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.map f)).app
          (gamma.obj i) ≫
        ((ComposableArrows.mk₁ zeta).obj
          ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.obj j)).map
            (gamma.map f) := rfl

/-- These are the three actual coefficients in the displayed all-time map. -/
theorem nerveNT_map_zero_zero (x : C) :
    ((ComposableArrows.mk₁ zeta).map
      (homOfLE (show (0 : Fin 2) ≤ 0 from le_rfl))).app x = 𝟙 (A.obj x) := rfl

theorem nerveNT_map_zero_one (x : C) :
    ((ComposableArrows.mk₁ zeta).map
      (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))).app x = zeta.app x := rfl

theorem nerveNT_map_one_one (x : C) :
    ((ComposableArrows.mk₁ zeta).map
      (homOfLE (show (1 : Fin 2) ≤ 1 from le_rfl))).app x = 𝟙 (B.obj x) := rfl

theorem nerveNT_zero : SSet.ι₀ ≫ (natTransHomotopy zeta).h = nerveMap A :=
  (natTransHomotopy zeta).h₀

theorem nerveNT_one : SSet.ι₁ ≫ (natTransHomotopy zeta).h = nerveMap B :=
  (natTransHomotopy zeta).h₁

theorem nerveNT_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (gamma : (nerve C).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (nerve D).map e ((natTransHomotopy zeta).h.app k (gamma, s)) =
      (natTransHomotopy zeta).h.app l
        ((nerve C).map e gamma, (SSet.stdSimplex.obj ⦋1⦌).map e s) := rfl

/-- The actual existing realization and singularization maps at every time. -/
theorem nerveNTR_map_formula :
    (natTransHomotopyR zeta).h =
      R.obj (nerve C) ◁ SSet.stdSimplex.toSSetObjI ≫
        (Functor.Monoidal.μIso TopCat.toSSet (SSet.toTop.obj (nerve C)) TopCat.I).hom ≫
          TopCat.toSSet.map
            ((SSet.stdSimplex.toTopTensorDeltaOneIso (nerve C)).inv ≫
              SSet.toTop.map (natTransMap zeta)) := rfl

theorem nerveNTR_zero : SSet.ι₀ ≫ (natTransHomotopyR zeta).h = R.map (nerveMap A) :=
  (natTransHomotopyR zeta).h₀

theorem nerveNTR_one : SSet.ι₁ ≫ (natTransHomotopyR zeta).h = R.map (nerveMap B) :=
  (natTransHomotopyR zeta).h₁

theorem nerveNTR_time_formula (k : SimplexCategoryᵒᵖ)
    (x : (R.obj (nerve C)).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (natTransHomotopyR zeta).h.app k (x, s) =
      (R.obj (nerve C) ◁ SSet.stdSimplex.toSSetObjI ≫
        (Functor.Monoidal.μIso TopCat.toSSet (SSet.toTop.obj (nerve C)) TopCat.I).hom ≫
          TopCat.toSSet.map
            ((SSet.stdSimplex.toTopTensorDeltaOneIso (nerve C)).inv ≫
              SSet.toTop.map (natTransMap zeta))).app k (x, s) := rfl

theorem nerveNTR_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (x : (R.obj (nerve C)).obj k) (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (R.obj (nerve D)).map e ((natTransHomotopyR zeta).h.app k (x, s)) =
      (natTransHomotopyR zeta).h.app l
        ((R.obj (nerve C)).map e x, (SSet.stdSimplex.obj ⦋1⦌).map e s) :=
  (congrFun ((natTransHomotopyR zeta).h.naturality e) (x, s)).symm

end FormulaWrappers

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
variable (t : (flagHom X a b).obj (op ⦋n⦌))

/-- The five actual supplied NTs instantiate the same formula wrappers. -/
abbrev fiberAlphaNerveHomotopy := natTransHomotopy (fiberAlpha X a b n t)
abbrev fiberBetaNerveHomotopy := natTransHomotopy (fiberToCenter X a b n t)
abbrev fiberTerminalNerveHomotopy := natTransHomotopy (fiberTerminalNatTrans X a b n t)
abbrev fiberKappaNerveHomotopy := natTransHomotopy (fiberCollapseCenterIso X a b n t).hom
abbrev fiberDeltaNerveHomotopy := natTransHomotopy (fiberCenterCollapseIso X a b n t).hom

abbrev fiberAlphaRH := natTransHomotopyR (fiberAlpha X a b n t)
abbrev fiberBetaRH := natTransHomotopyR (fiberToCenter X a b n t)
abbrev fiberTerminalRH := natTransHomotopyR (fiberTerminalNatTrans X a b n t)
abbrev fiberKappaRH := natTransHomotopyR (fiberCollapseCenterIso X a b n t).hom
abbrev fiberDeltaRH := natTransHomotopyR (fiberCenterCollapseIso X a b n t).hom

/-- Reverse only the internal fibrant ihom Edge, retaining its chosen filler. -/
def fiberReturnEdge :
    SSet.KanComplex.FundamentalGroupoid.Edge
      (X := (ihom (R.obj (nerve (Fiber X a b n t)))).obj
        (R.obj (nerve (Fiber X a b n t))))
      (.mk (SSet.ihom₀Equiv.symm
        (R.map (nerveMap (fiberCollapseFunctor X a b n t ⋙ fiberCenterFunctor X a b n t)))))
      (.mk (SSet.ihom₀Equiv.symm (R.map (nerveMap (𝟭 (Fiber X a b n t)))))) :=
  (SSet.Homotopy.equiv (fiberKappaRH X a b n t)).comp
    ((SSet.Homotopy.equiv (fiberBetaRH X a b n t)).inv.comp
      (SSet.Homotopy.equiv (fiberAlphaRH X a b n t)))

/-- The first inverse field has the exact composite-Edge map, not an opaque zigzag. -/
def fiberHomInvId :
    SSet.Homotopy (R.map (fiberCollapse X a b n t) ≫ R.map (fiberSection X a b n t))
      (𝟙 (R.obj (nerve (Fiber X a b n t)))) :=
  (SSet.Homotopy.equiv.symm (fiberReturnEdge X a b n t)).congr
    (Functor.map_comp R (fiberCollapse X a b n t) (fiberSection X a b n t))
    (CategoryTheory.Functor.map_id R (nerve (Fiber X a b n t)))

/-- The second inverse field uses the actual point-side NT and its R time map. -/
def fiberInvHomId :
    SSet.Homotopy (R.map (fiberSection X a b n t) ≫ R.map (fiberCollapse X a b n t))
      (𝟙 (R.obj (nerve fiberPointCat.{u}))) :=
  (fiberDeltaRH X a b n t).congr
    (Functor.map_comp R (fiberSection X a b n t) (fiberCollapse X a b n t))
    (CategoryTheory.Functor.map_id R (nerve fiberPointCat.{u}))

theorem fiberHomInvId_zero :
    SSet.ι₀ ≫ (fiberHomInvId X a b n t).h =
      R.map (fiberCollapse X a b n t) ≫ R.map (fiberSection X a b n t) :=
  (fiberHomInvId X a b n t).h₀

theorem fiberHomInvId_one :
    SSet.ι₁ ≫ (fiberHomInvId X a b n t).h = 𝟙 (R.obj (nerve (Fiber X a b n t))) :=
  (fiberHomInvId X a b n t).h₁

theorem fiberInvHomId_zero :
    SSet.ι₀ ≫ (fiberInvHomId X a b n t).h =
      R.map (fiberSection X a b n t) ≫ R.map (fiberCollapse X a b n t) :=
  (fiberInvHomId X a b n t).h₀

theorem fiberInvHomId_one :
    SSet.ι₁ ≫ (fiberInvHomId X a b n t).h = 𝟙 (R.obj (nerve fiberPointCat.{u})) :=
  (fiberInvHomId X a b n t).h₁

theorem fiberHomInvId_map :
    (fiberHomInvId X a b n t).h =
      MonoidalClosed.uncurry (fiberReturnEdge X a b n t).map := rfl

theorem fiberHomInvId_time (k : SimplexCategoryᵒᵖ)
    (x : (R.obj (nerve (Fiber X a b n t))).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (fiberHomInvId X a b n t).h.app k (x, s) =
      (MonoidalClosed.uncurry (fiberReturnEdge X a b n t).map).app k (x, s) := rfl

theorem fiberHomInvId_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (x : (R.obj (nerve (Fiber X a b n t))).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (R.obj (nerve (Fiber X a b n t))).map e
        ((fiberHomInvId X a b n t).h.app k (x, s)) =
      (MonoidalClosed.uncurry (fiberReturnEdge X a b n t).map).app l
        ((R.obj (nerve (Fiber X a b n t))).map e x,
          (SSet.stdSimplex.obj ⦋1⦌).map e s) :=
  (congrFun ((fiberHomInvId X a b n t).h.naturality e) (x, s)).symm

theorem fiberInvHomId_map :
    (fiberInvHomId X a b n t).h = (fiberDeltaRH X a b n t).h := rfl

theorem fiberInvHomId_time (k : SimplexCategoryᵒᵖ)
    (x : (R.obj (nerve fiberPointCat.{u})).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (fiberInvHomId X a b n t).h.app k (x, s) =
      (R.obj (nerve fiberPointCat.{u}) ◁ SSet.stdSimplex.toSSetObjI ≫
        (Functor.Monoidal.μIso TopCat.toSSet
          (SSet.toTop.obj (nerve fiberPointCat.{u})) TopCat.I).hom ≫
            TopCat.toSSet.map
              ((SSet.stdSimplex.toTopTensorDeltaOneIso (nerve fiberPointCat.{u})).inv ≫
                SSet.toTop.map
                  (natTransMap (fiberCenterCollapseIso X a b n t).hom))).app k (x, s) :=
  nerveNTR_time_formula (fiberCenterCollapseIso X a b n t).hom k x s

theorem fiberInvHomId_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (x : (R.obj (nerve fiberPointCat.{u})).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (R.obj (nerve fiberPointCat.{u})).map e ((fiberInvHomId X a b n t).h.app k (x, s)) =
      (fiberDeltaRH X a b n t).h.app l
        ((R.obj (nerve fiberPointCat.{u})).map e x, (SSet.stdSimplex.obj ⦋1⦌).map e s) :=
  nerveNTR_operator (fiberCenterCollapseIso X a b n t).hom e x s

/-- Both actual inverse fields for the same collapse and same center section. -/
def fiberHomotopyEquiv :
    SSet.HomotopyEquiv (R.obj (nerve (Fiber X a b n t)))
      (R.obj (nerve fiberPointCat.{u})) where
  hom := R.map (fiberCollapse X a b n t)
  inv := R.map (fiberSection X a b n t)
  homInvId := fiberHomInvId X a b n t
  invHomId := fiberInvHomId X a b n t

theorem fiberHomotopyEquiv_hom :
    (fiberHomotopyEquiv X a b n t).hom = R.map (fiberCollapse X a b n t) := rfl

theorem fiberHomotopyEquiv_inv :
    (fiberHomotopyEquiv X a b n t).inv = R.map (fiberSection X a b n t) := rfl

theorem fiber_collapse_geometric :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapse X a b n t))) :=
  SSet.KanComplex.W.homotopyEquivHom (fiberHomotopyEquiv X a b n t)

end

end DaggerOriginalFlagFlankification
