import OriginalNecklaceSimple
import ChosenNecklacesOver

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {A X : SSet.{u}} (j : A ⟶ X) (hj : NecklaceSimple j)
  {a b : A.obj (op ⦋0⦌)}

include hj in
/-- The full original over-target necklace lifts without changing its code or endpoints. -/
theorem exists_simpleLift (P : NecklacesOver X (j.app _ a) (j.app _ b)) :
    ∃ l : P.code.toSSet ⟶ A, l ≫ j = P.map ∧
      l.app _ P.code.first = a ∧ l.app _ P.code.last = b := by
  obtain ⟨l, hl, h0, h1⟩ := hj P.code (SSet.yonedaEquiv.symm a)
    (SSet.yonedaEquiv.symm b) P.map
    (by
      apply SSet.yonedaEquiv.injective
      simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
        SSet.yonedaEquiv.apply_symm_apply] using P.first)
    (by
      apply SSet.yonedaEquiv.injective
      simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
        SSet.yonedaEquiv.apply_symm_apply] using P.last)
  refine ⟨l, hl, ?_, ?_⟩
  · simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
      SSet.yonedaEquiv.apply_symm_apply] using congrArg SSet.yonedaEquiv h0
  · simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
      SSet.yonedaEquiv.apply_symm_apply] using congrArg SSet.yonedaEquiv h1

def simpleLiftMap (P : NecklacesOver X (j.app _ a) (j.app _ b)) : P.code.toSSet ⟶ A :=
  Classical.choose (exists_simpleLift j hj P)

theorem simpleLift_fac (P : NecklacesOver X (j.app _ a) (j.app _ b)) :
    simpleLiftMap j hj P ≫ j = P.map :=
  (Classical.choose_spec (exists_simpleLift j hj P)).1

def simpleLiftObj (P : NecklacesOver X (j.app _ a) (j.app _ b)) : NecklacesOver A a b where
  code := P.code
  map := simpleLiftMap j hj P
  first := (Classical.choose_spec (exists_simpleLift j hj P)).2.1
  last := (Classical.choose_spec (exists_simpleLift j hj P)).2.2

variable [Mono j]

/-- Monicity lifts every original over-target arrow with its actual underlying necklace map. -/
def simpleLiftHom {P Q : NecklacesOver X (j.app _ a) (j.app _ b)} (h : P ⟶ Q) :
    simpleLiftObj j hj P ⟶ simpleLiftObj j hj Q where
  hom := h.hom
  w := by
    apply (cancel_mono j).mp
    change (h.hom.map ≫ simpleLiftMap j hj Q) ≫ j = simpleLiftMap j hj P ≫ j
    rw [Category.assoc, simpleLift_fac, simpleLift_fac]
    exact h.w

def simpleLiftFunctor : NecklacesOver X (j.app _ a) (j.app _ b) ⥤ NecklacesOver A a b where
  obj := simpleLiftObj j hj
  map := simpleLiftHom j hj
  map_id _ := NecklacesOver.Hom.ext rfl
  map_comp _ _ := NecklacesOver.Hom.ext rfl

/-- Lifting after the original postcomposition gives the same necklace over A. -/
def simpleLiftPostcompHom (P : NecklacesOver A a b) :
    simpleLiftObj j hj ((NecklacesOver.postcomp j).obj P) ⟶ P where
  hom := NecklaceCode.Hom.id P.code
  w := by
    apply (cancel_mono j).mp
    change (𝟙 _ ≫ P.map) ≫ j =
      simpleLiftMap j hj ((NecklacesOver.postcomp j).obj P) ≫ j
    rw [Category.id_comp, simpleLift_fac]
    rfl

omit [Mono j] in
/-- Postcomposing the lifted object gives the same necklace over X. -/
def simplePostcompLiftHom (P : NecklacesOver X (j.app _ a) (j.app _ b)) :
    (NecklacesOver.postcomp j).obj (simpleLiftObj j hj P) ⟶ P where
  hom := NecklaceCode.Hom.id P.code
  w := by
    change 𝟙 _ ≫ P.map = simpleLiftMap j hj P ≫ j
    rw [Category.id_comp, simpleLift_fac]

end

end DaggerOriginalProductGadget
