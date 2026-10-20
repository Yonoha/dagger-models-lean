import WholeWitnessSides
import TriangleWitnessStageEquations

/-! Both complete triangle squares for an actual original arrow factorization. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial
open DaggerSimplexInverseWitnessCategory DaggerWholeWitnessSides
open DaggerNativeIhomHoObjects
universe u v w
namespace DaggerWholeWitnessTriangleStageLifts

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]

theorem triangle_squares_eventually (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {F : J ⥤ Witness R} {c : Cocone F} (hc : IsColimit c)
    (X : Witness R)
    (hX : ∀ b, IsCardinalPresentable (side R X b ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (side R X b ⊗ Δ[2]) κ)
    (h : X ⟶ c.pt) {i : J} (a : X.arrow ⟶ (F.obj i).arrow)
    (hfac : a ≫ (c.ι.app i).square = h.square) :
    ∃ (j : J) (t : i ⟶ j), ∀ b,
      TriangleSquare (sideMap R (a ≫ (F.map t).square) b)
        (triangles R X b) (triangles R (F.obj j) b) := by
  let D : ULift.{u} Bool → J ⥤ SSet.{u} := fun b ↦ F ⋙ sideFunctor R b.down
  let cc := fun b : ULift.{u} Bool ↦ (sideFunctor R b.down).mapCocone c
  have hh : ∀ b : ULift.{u} Bool, TriangleSquare
      (sideMap R a b.down ≫ (cc b).ι.app i)
      (triangles R X b.down) (triangles R c.pt b.down) := by
    intro b
    change TriangleSquare (sideMap R a b.down ≫ sideMap R (c.ι.app i).square b.down) _ _
    rw [← sideMap_comp, hfac]
    exact triangleSquare_hom R h b.down
  obtain ⟨j, t, ht⟩ := DaggerTriangleWitnessStageEquations.finite_triangle_squares κ
    (fun b : ULift.{u} Bool ↦ side R X b.down) D cc
    (fun b ↦ sideIsColimit R hc b.down) (fun b ↦ hX b.down)
    (fun b ↦ homObject (sourceEnd R X b.down))
    (fun b ↦ homObject (𝟙 (side R X b.down))) (fun b ↦ triangles R X b.down)
    (fun b j ↦ homObject (sourceEnd R (F.obj j) b.down))
    (fun b j ↦ homObject (𝟙 (side R (F.obj j) b.down)))
    (fun b j ↦ triangles R (F.obj j) b.down)
    (fun b ↦ homObject (sourceEnd R c.pt b.down))
    (fun b ↦ homObject (𝟙 (side R c.pt b.down))) (fun b ↦ triangles R c.pt b.down)
    (fun b j ↦ triangleSquare_hom R (c.ι.app j) b.down)
    (fun b {_ _} t ↦ triangleSquare_hom R (F.map t) b.down)
    (fun b ↦ sideMap R a b.down) hh
  refine ⟨j, t, fun b ↦ ?_⟩
  rw [sideMap_comp]
  exact ht (ULift.up b)

end DaggerWholeWitnessTriangleStageLifts
