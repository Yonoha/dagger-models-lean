import OriginalFlagFiberContractionChecks

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerOriginalFlagFlankification DaggerNerveHomotopy

universe u v

noncomputable section

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)),
    classOf X a b n (fiberCenterObj X a b n t).obj = t := fiberCenterObj_class

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)),
    SSet.Homotopy (R.map (fiberCollapse X a b n t) ≫ R.map (fiberSection X a b n t))
      (𝟙 (R.obj (nerve (Fiber X a b n t)))) := fiberHomInvId

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)),
    SSet.Homotopy (R.map (fiberSection X a b n t) ≫ R.map (fiberCollapse X a b n t))
      (𝟙 (R.obj (nerve fiberPointCat.{u}))) := fiberInvHomId

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)),
    (fiberHomotopyEquiv X a b n t).hom = R.map (fiberCollapse X a b n t) ∧
      (fiberHomotopyEquiv X a b n t).inv = R.map (fiberSection X a b n t) :=
  fun X a b n t ↦ ⟨fiberHomotopyEquiv_hom X a b n t, fiberHomotopyEquiv_inv X a b n t⟩

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌))
    (k l : SimplexCategoryᵒᵖ) (e : k ⟶ l)
    (x : (R.obj (nerve (Fiber X a b n t))).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k),
    (R.obj (nerve (Fiber X a b n t))).map e
        ((fiberHomInvId X a b n t).h.app k (x, s)) =
      (MonoidalClosed.uncurry (fiberReturnEdge X a b n t).map).app l
        ((R.obj (nerve (Fiber X a b n t))).map e x,
          (SSet.stdSimplex.obj ⦋1⦌).map e s) :=
  fun X a b n t _ _ e x s ↦ fiberHomInvId_operator X a b n t e x s

example : ∀ (k : SimplexCategoryᵒᵖ) (s : (Δ[0] : SSet.{u}).obj k),
    fiberPointNerveIsoDelta0.inv.app k s =
      discreteConstantChain (PUnit.{u+1}) k PUnit.unit := fiberPointNerveIsoDelta0_inv_app

example : ∀ (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
    (t : (DaggerChosenRigidificationNecklace.flagHom X a b).obj (op ⦋n⦌)),
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapse X a b n t))) ∧
      fiberCollapseDelta0 X a b n t =
        SSet.stdSimplex.isTerminalObj₀.from (nerve (Fiber X a b n t)) ∧
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapseDelta0 X a b n t))) :=
  fun X a b n t ↦ ⟨fiber_collapse_geometric X a b n t,
    fiberCollapseDelta0_triangle X a b n t, fiber_delta0_collapse_geometric X a b n t⟩

example : ∀ (X : SSet.{0}) (a : X.obj (op ⦋0⦌))
    (t : (DaggerChosenRigidificationNecklace.flagHom X a a).obj (op ⦋0⦌)),
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapseDelta0 X a a 0 t))) :=
  fun X a t ↦ fiber_delta0_collapse_geometric X a a 0 t

end
