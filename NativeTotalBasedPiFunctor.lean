import TopCatModelCategory.SSet.HomotopyGroup
import TopCatModelCategory.SSet.PiZero

/-! The genuine total based-pi functor uses every original vertex and the original mapPi. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open SSet.KanComplex
universe u
namespace DaggerNativeTotalBasedPiFunctor
noncomputable section

def totalPiFunctor (n : ℕ) : SSet.{u} ⥤ Type u where
  obj X := Σ x : X _⦋0⦌, π n X x
  map f s := ⟨f.app _ s.1, mapπ f n s.1 _ rfl s.2⟩
  map_id X := by
    funext ⟨x, s⟩
    exact Sigma.ext rfl (heq_of_eq (mapπ_id n x s))
  map_comp f g := by
    funext ⟨x, s⟩
    exact Sigma.ext rfl (heq_of_eq (mapπ_mapπ f n x _ rfl g _ rfl s).symm)

def vertexProjection (n : ℕ) : totalPiFunctor.{u} n ⟶ SSet.evaluation.obj (op ⦋0⦌) where
  app _ s := s.1
  naturality _ _ _ := rfl

theorem totalPiFunctor_map (n : ℕ) {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : X _⦋0⦌) (s : π n X x) :
    (totalPiFunctor n).map f ⟨x, s⟩ = ⟨f.app _ x, mapπ f n x _ rfl s⟩ := rfl

theorem vertexProjection_app (n : ℕ) (X : SSet.{u}) (x : X _⦋0⦌) (s : π n X x) :
    (vertexProjection n).app X ⟨x, s⟩ = x := rfl

end
end DaggerNativeTotalBasedPiFunctor
