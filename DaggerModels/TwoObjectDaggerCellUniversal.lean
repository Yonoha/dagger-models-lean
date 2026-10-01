import DaggerModels.TwoObjectDaggerCell

/-! A short, implementation-independent specification for `bg.eq.A-univ`.
The proof supplies the actual finite-path free cell on the two-object graph. -/

open CategoryTheory MonoidalCategory

universe u

namespace DaggerModels
namespace DaggerSimplicialCat

/-- Read the images of two objects and a generating simplicial map under every dagger functor. -/
def classifyTwoObjectCell {K : SSet.{u}} {C D : DaggerSimplicialCat.{u, u}}
    (x y : C.Obj) (i : K ⟶ (x ⟶[SSet.{u}] y)) (F : Hom C D) :
    Σ a : D.Obj, Σ b : D.Obj, (K ⟶ (a ⟶[SSet.{u}] b)) :=
  ⟨F.obj x, F.obj y, i ≫ F.map x y⟩

end DaggerSimplicialCat

/-- The two-object cell represents all pairs of objects and all generating simplicial maps. -/
theorem exists_twoObjectDaggerCell (K : SSet.{u}) :
    ∃ (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj)
      (i : K ⟶ (x ⟶[SSet.{u}] y)), ∀ D : DaggerSimplicialCat.{u, u},
        Function.Bijective (DaggerSimplicialCat.classifyTwoObjectCell x y i (D := D)) := by
  refine ⟨TwoObjectDaggerCell.cell K, TwoObjectDaggerGraph.left,
    TwoObjectDaggerGraph.right, TwoObjectDaggerCell.generator K, ?_⟩
  intro D
  exact (TwoObjectDaggerCell.homEquiv K D).bijective

end DaggerModels
