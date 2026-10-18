import OriginalFlagFiberContraction
import OriginalFlagDiscreteNerve
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace DaggerNerveHomotopy

/-- The unique map into the literal constant PUnit simplicial set. -/
def fiberPointConstantFrom (Y : SSet.{u}) : Y ⟶ constantSSet (PUnit.{u+1}) where
  app _ _ := PUnit.unit
  naturality _ _ _ := rfl

theorem fiberPointConstantFrom_app (Y : SSet.{u}) (k : SimplexCategoryᵒᵖ)
    (y : Y.obj k) : (fiberPointConstantFrom Y).app k y = PUnit.unit := rfl

def fiberPointConstantIsTerminal : IsTerminal (constantSSet (PUnit.{u+1})) :=
  IsTerminal.ofUniqueHom fiberPointConstantFrom (fun Y f ↦ by
    apply NatTrans.ext
    funext k y
    change (f.app k y : PUnit.{u+1}) = PUnit.unit
    exact @Subsingleton.elim (PUnit.{u+1}) inferInstance _ _)

/-- The same point nerve, with a genuine simplicial inverse to Delta[0]. -/
def fiberPointNerveIsoDelta0 : nerve fiberPointCat.{u} ≅ (Δ[0] : SSet.{u}) :=
  nerveDiscreteIso (PUnit.{u+1}) ≪≫
    fiberPointConstantIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

theorem fiberPointNerveIsoDelta0_hom_inv :
    fiberPointNerveIsoDelta0.hom ≫ fiberPointNerveIsoDelta0.inv =
      𝟙 (nerve fiberPointCat.{u}) := fiberPointNerveIsoDelta0.hom_inv_id

theorem fiberPointNerveIsoDelta0_inv_hom :
    fiberPointNerveIsoDelta0.inv ≫ fiberPointNerveIsoDelta0.hom =
      𝟙 (Δ[0] : SSet.{u}) := fiberPointNerveIsoDelta0.inv_hom_id

theorem fiberPointNerveIsoDelta0_hom :
    fiberPointNerveIsoDelta0.hom =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem fiberPointNerveIsoDelta0_hom_app (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve fiberPointCat.{u}).obj k) :
    fiberPointNerveIsoDelta0.hom.app k gamma =
      (Δ[0] : SSet.{u}).map ((k.unop.const _ 0).op)
        (SSet.stdSimplex.obj₀Equiv.symm 0) := by
  rw [fiberPointNerveIsoDelta0_hom]
  rfl

theorem fiberPointNerveIsoDelta0_inv_app (k : SimplexCategoryᵒᵖ)
    (s : (Δ[0] : SSet.{u}).obj k) :
    fiberPointNerveIsoDelta0.inv.app k s =
      discreteConstantChain (PUnit.{u+1}) k PUnit.unit := by
  apply nerve.ext_of_isThin
  funext i
  apply Discrete.ext
  exact Subsingleton.elim _ _

/-- Every operator is retained, including operators whose image of zero is nonzero. -/
theorem fiberPointNerveIsoDelta0_hom_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (gamma : (nerve fiberPointCat.{u}).obj k) :
    (Δ[0] : SSet.{u}).map e (fiberPointNerveIsoDelta0.hom.app k gamma) =
      fiberPointNerveIsoDelta0.hom.app l ((nerve fiberPointCat.{u}).map e gamma) :=
  (congrFun (fiberPointNerveIsoDelta0.hom.naturality e) gamma).symm

theorem fiberPointNerveIsoDelta0_inv_operator {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (s : (Δ[0] : SSet.{u}).obj k) :
    (nerve fiberPointCat.{u}).map e (fiberPointNerveIsoDelta0.inv.app k s) =
      discreteConstantChain (PUnit.{u+1}) l PUnit.unit := by
  rw [fiberPointNerveIsoDelta0_inv_app]
  change (nerve fiberPointCat.{u}).map e
      ((nerveDiscreteIso (PUnit.{u+1})).inv.app k PUnit.unit) =
    (nerveDiscreteIso (PUnit.{u+1})).inv.app l PUnit.unit
  exact nerveDiscreteIso_inv_naturality (PUnit.{u+1}) e PUnit.unit

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)
variable (t : (flagHom X a b).obj (op ⦋n⦌))

/-- The original collapse followed by the displayed genuine point comparison. -/
def fiberCollapseDelta0 : nerve (Fiber X a b n t) ⟶ (Δ[0] : SSet.{u}) :=
  fiberCollapse X a b n t ≫ fiberPointNerveIsoDelta0.hom

theorem fiberCollapseDelta0_triangle :
    fiberCollapseDelta0 X a b n t =
      SSet.stdSimplex.isTerminalObj₀.from (nerve (Fiber X a b n t)) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem fiberCollapseDelta0_app (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Fiber X a b n t)).obj k) :
    (fiberCollapseDelta0 X a b n t).app k gamma =
      (Δ[0] : SSet.{u}).map ((k.unop.const _ 0).op)
        (SSet.stdSimplex.obj₀Equiv.symm 0) :=
  fiberPointNerveIsoDelta0_hom_app k ((fiberCollapse X a b n t).app k gamma)

/-- No opaque replacement of the original forward map occurs in this equivalence. -/
def fiberDelta0HomotopyEquiv :
    SSet.HomotopyEquiv (R.obj (nerve (Fiber X a b n t))) (R.obj (Δ[0] : SSet.{u})) :=
  (fiberHomotopyEquiv X a b n t).trans
    (SSet.HomotopyEquiv.ofIso (R.mapIso fiberPointNerveIsoDelta0))

theorem fiberDelta0HomotopyEquiv_hom :
    (fiberDelta0HomotopyEquiv X a b n t).hom = R.map (fiberCollapseDelta0 X a b n t) := by
  change R.map (fiberCollapse X a b n t) ≫ R.map fiberPointNerveIsoDelta0.hom =
    R.map (fiberCollapse X a b n t ≫ fiberPointNerveIsoDelta0.hom)
  exact (Functor.map_comp R _ _).symm

theorem fiberDelta0HomotopyEquiv_inv :
    (fiberDelta0HomotopyEquiv X a b n t).inv =
      R.map fiberPointNerveIsoDelta0.inv ≫ R.map (fiberSection X a b n t) := rfl

theorem fiber_delta0_collapse_geometric :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fiberCollapseDelta0 X a b n t))) := by
  change SSet.KanComplex.W (R.map (fiberCollapseDelta0 X a b n t))
  rw [← fiberDelta0HomotopyEquiv_hom]
  exact SSet.KanComplex.W.homotopyEquivHom (fiberDelta0HomotopyEquiv X a b n t)

end

end DaggerOriginalFlagFlankification
