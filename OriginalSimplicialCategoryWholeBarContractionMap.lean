import OriginalSimplicialCategoryBarCoproductDegrees

/-!
# Assemble the actual original component cylinders on the entire original bar

Use the native coproduct degree equivalence to retain the original endpoint,
apply its actual component cylinder, and return through the same equivalence.
Every original degree operator preserves this construction.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerOriginalSimplicialCategoryBarContractionMap
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarContractionMap
noncomputable section

/-- The cylinder in a whole original bar degree retains its same original endpoint. -/
def wholeBarCylinderDegree (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (p : (bar C ⊗ Δ[1]).obj n) : (bar C).obj n :=
  let a := (barDegreeEquiv C n).symm p.1
  barDegreeEquiv C n ⟨a.1, (barContractionMap C a.1).app n (a.2, p.2)⟩

/-- On each original component the whole cylinder is exactly its actual component cylinder. -/
theorem wholeBarCylinderDegree_apply (C : SimplicialCat.{u, u})
    (n : SimplexCategoryᵒᵖ) (y : C.Obj) (a : (barComponent C y).obj n)
    (t : Δ[1].obj n) :
    wholeBarCylinderDegree C n (barDegreeEquiv C n ⟨y, a⟩, t) =
      barDegreeEquiv C n ⟨y, (barContractionMap C y).app n (a, t)⟩ := by
  unfold wholeBarCylinderDegree
  rw [Equiv.symm_apply_apply]

/-- The assembled original endpoint cylinders respect every original degree operator. -/
theorem wholeBarCylinderDegree_natural (C : SimplicialCat.{u, u})
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) (p : (bar C ⊗ Δ[1]).obj n) :
    wholeBarCylinderDegree C m ((bar C ⊗ Δ[1]).map i p) =
      (bar C).map i (wholeBarCylinderDegree C n p) := by
  rcases p with ⟨a, t⟩
  obtain ⟨⟨y, a⟩, rfl⟩ := (barDegreeEquiv C n).surjective a
  change wholeBarCylinderDegree C m
      ((bar C).map i (barDegreeEquiv C n ⟨y, a⟩), Δ[1].map i t) =
    (bar C).map i (wholeBarCylinderDegree C n (barDegreeEquiv C n ⟨y, a⟩, t))
  rw [show (bar C).map i (barDegreeEquiv C n ⟨y, a⟩) =
      barDegreeEquiv C m ⟨y, (barComponent C y).map i a⟩ from
        coproductDegreeEquiv_map (barComponent C) i y a]
  rw [wholeBarCylinderDegree_apply, wholeBarCylinderDegree_apply]
  have hd := coproductDegreeEquiv_map (barComponent C) i y
    ((barContractionMap C y).app n (a, t))
  change (bar C).map i (barDegreeEquiv C n
      ⟨y, (barContractionMap C y).app n (a, t)⟩) = _ at hd
  rw [hd]
  exact congrArg (fun b ↦ barDegreeEquiv C m ⟨y, b⟩)
    (congrFun ((barContractionMap C y).naturality i) (a, t))

/-- The actual cylinder map on the whole original native coproduct bar. -/
def wholeBarContractionMap (C : SimplicialCat.{u, u}) : bar C ⊗ Δ[1] ⟶ bar C where
  app := wholeBarCylinderDegree C
  naturality _ _ i := by
    funext p
    exact wholeBarCylinderDegree_natural C i p

end
end DaggerOriginalSimplicialCategoryWholeBarContractionMap
