import OriginalSimplicialCategoryWholeBarLocalization

/-!
# Every strict fibre of the actual whole original bar projection

Use the original source-vertex subcomplex and the actual whole projection.
Every fibre simplex has the original coproduct endpoint and lies in its
original component fibre. Native coproduct decomposition gives the inverse.
No homotopy-fibre or quasifibration assertion is assumed.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarFibre
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarFibreDegree
noncomputable section

/-- The actual inverse image of the original source vertex under the whole bar projection. -/
def wholeBarFibre (C : SimplicialCat.{u, u}) (x : C.Obj) : (bar C).Subcomplex :=
  (sourceVertexSubcomplex C x).preimage (barProjection C)

/-- Whole-fibre membership retains the exact original projection equation. -/
theorem wholeBarFibre_mem (C : SimplicialCat.{u, u}) (x : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : (bar C).obj n) :
    a ∈ (wholeBarFibre C x).obj n ↔
      (barProjection C).app n a = constantSourceSimplex C x n := Iff.rfl

/-- Each actual component fibre includes in the actual whole original fibre. -/
def componentFibreInclusion (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (barFibre C x y).toSSet ⟶ (wholeBarFibre C x).toSSet where
  app n a := ⟨(barInclusion C y).app n a.val, by
    change (barProjection C).app n ((barInclusion C y).app n a.val) =
      constantSourceSimplex C x n
    exact (congrFun (NatTrans.congr_app (barInclusion_projection C y) n) a.val).trans
      a.property⟩
  naturality _ _ i := by
    funext a
    apply Subtype.ext
    exact congrFun ((barInclusion C _).naturality i) a.val

/-- The component-fibre inclusion retains the actual whole bar inclusion. -/
theorem componentFibreInclusion_ι (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    componentFibreInclusion C x y ≫ (wholeBarFibre C x).ι =
      (barFibre C x y).ι ≫ barInclusion C y := by
  apply NatTrans.ext
  funext n
  rfl

/-- The native coproduct contains every original endpoint component fibre. -/
def componentFibreSum (C : SimplicialCat.{u, u}) (x : C.Obj) : SSet.{u} :=
  ∐ (fun y ↦ (barFibre C x y).toSSet)

/-- Descend all actual component-fibre inclusions to the actual whole fibre. -/
def componentFibreSumMap (C : SimplicialCat.{u, u}) (x : C.Obj) :
    componentFibreSum C x ⟶ (wholeBarFibre C x).toSSet :=
  Sigma.desc (componentFibreInclusion C x)

/-- Erasing fibre membership keeps the original endpoint and simplex injectively. -/
theorem componentFibreSigma_injective (C : SimplicialCat.{u, u}) (x : C.Obj)
    (n : SimplexCategoryᵒᵖ) :
    Function.Injective (fun a : Σ y, ((barFibre C x y).toSSet).obj n ↦
      (⟨a.1, a.2.val⟩ : Σ y, (barComponent C y).obj n)) := by
  rintro ⟨y, a⟩ ⟨z, b⟩ h
  have hs := Sigma.mk.inj h
  cases hs.1
  have hab : a = b := Subtype.ext (eq_of_heq hs.2)
  cases hab
  rfl

/-- Every whole-fibre simplex corresponds to exactly one original endpoint and fibre simplex. -/
def wholeBarFibreComponentEquiv (C : SimplicialCat.{u, u}) (x : C.Obj)
    (n : SimplexCategoryᵒᵖ) :
    (Σ y, ((barFibre C x y).toSSet).obj n) ≃ ((wholeBarFibre C x).toSSet).obj n where
  toFun a := ⟨barDegreeEquiv C n ⟨a.1, a.2.val⟩, by
    change (barProjection C).app n (barDegreeEquiv C n ⟨a.1, a.2.val⟩) =
      constantSourceSimplex C x n
    exact (barDegreeEquiv_projection C n a.1 a.2.val).trans a.2.property⟩
  invFun b :=
    let a := (barDegreeEquiv C n).symm b.val
    ⟨a.1, ⟨a.2, by
      change (barComponentProjection C a.1).app n a.2 = constantSourceSimplex C x n
      calc
        _ = (barProjection C).app n (barDegreeEquiv C n ⟨a.1, a.2⟩) :=
          (barDegreeEquiv_projection C n a.1 a.2).symm
        _ = (barProjection C).app n b.val := congrArg ((barProjection C).app n)
          ((barDegreeEquiv C n).apply_symm_apply b.val)
        _ = constantSourceSimplex C x n := b.property⟩⟩
  left_inv := by
    rintro ⟨y, a⟩
    apply componentFibreSigma_injective C x n
    exact (barDegreeEquiv C n).symm_apply_apply ⟨y, a.val⟩
  right_inv b := by
    apply Subtype.ext
    exact (barDegreeEquiv C n).apply_symm_apply b.val

/-- The actual native coproduct fibre degree is the actual whole inverse-image degree. -/
def componentFibreSumDegreeEquiv (C : SimplicialCat.{u, u}) (x : C.Obj)
    (n : SimplexCategoryᵒᵖ) :
    (componentFibreSum C x).obj n ≃ ((wholeBarFibre C x).toSSet).obj n :=
  (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n).symm.trans
    (wholeBarFibreComponentEquiv C x n)

/-- The whole degree equivalence retains the actual component-fibre inclusion. -/
theorem componentFibreSumDegreeEquiv_apply (C : SimplicialCat.{u, u}) (x y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : ((barFibre C x y).toSSet).obj n) :
    componentFibreSumDegreeEquiv C x n
        (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n ⟨y, a⟩) =
      (componentFibreInclusion C x y).app n a := by
  apply Subtype.ext
  change ((wholeBarFibreComponentEquiv C x n)
      ((coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n).symm
        (coproductDegreeEquiv (fun y ↦ (barFibre C x y).toSSet) n ⟨y, a⟩))).val = _
  rw [Equiv.symm_apply_apply]
  rfl

end
end DaggerOriginalSimplicialCategoryWholeBarFibreDegree
