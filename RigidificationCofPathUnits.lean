import RigidificationCofFacets

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

open SimplicialThickening

variable {J : Type u} [LinearOrder J]

theorem diagonal_path_singleton (i : J) (p : Path i i) : p.I = {i} := by
  ext x
  constructor
  · intro hx
    exact le_antisymm (p.le_right x hx) (p.left_le x hx)
  · intro hx
    exact hx ▸ p.left

/-- All diagonal simplices are the original enriched identity, in every degree. -/
theorem diagonal_simplex (i : J) (q : SimplexCategoryᵒᵖ) (γ : (hom i i).obj q) :
    γ = (SimplicialThickening.SimplicialCategory.id (.mk i)).app q PUnit.unit := by
  apply nerve.ext_of_isThin
  funext t
  apply Path.ext
  exact diagonal_path_singleton i (γ.obj t)

def diagonalIso (i : J) : 𝟙_ SSet.{u} ≅ hom i i where
  hom := SimplicialThickening.SimplicialCategory.id (.mk i)
  inv := SemiCartesianMonoidalCategory.toUnit _
  hom_inv_id := by
    apply NatTrans.ext
    funext q p
    cases p
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext q γ
    exact (diagonal_simplex i q γ).symm

def emptyHomMap {i j : J} (hji : j < i) (X : SSet.{u}) : hom i j ⟶ X where
  app _ γ := False.elim ((not_le_of_gt hji) (γ.obj 0).le)
  naturality _ _ _ := by
    funext γ
    exact False.elim ((not_le_of_gt hji) (γ.obj 0).le)

theorem empty_hom_ext {i j : J} (hji : j < i) {X : SSet.{u}} (f g : hom i j ⟶ X) :
    f = g := by
  apply NatTrans.ext
  funext q γ
  exact False.elim ((not_le_of_gt hji) (γ.obj 0).le)

end DaggerOrdinaryRigidificationCof.PathFacets
