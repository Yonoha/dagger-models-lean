import RectangularInverseDataPost
import FiniteStageEquations

/-! Strict rectangular cell refinements from equality in the actual colimit. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerRectangularInverseWitnessData DaggerNativeEndomorphismSimplexMaps
universe u
namespace DaggerRectangularCellStageRefinements

theorem equation_after_colimit {A B G X Y Z : SSet.{u}} {n : ℕ}
    (p : A ⟶ B) (a : A ⟶ G) (b : B ⟶ G) (hsource : p ≫ b = a)
    (q : X ⟶ Y) (x : X ⟶ Z) (y : Y ⟶ Z) (htarget : q ≫ y = x)
    (s : ((ihom A).obj X).obj (op ⦋n⦌))
    (t : ((ihom B).obj Y).obj (op ⦋n⦌))
    (z : ((ihom G).obj Z).obj (op ⦋n⦌))
    (hs : Square a x s z) (ht : Square b y t z) :
    (simplexHomEquiv A X n s ≫ q) ≫ y =
      (p ▷ Δ[n] ≫ simplexHomEquiv B Y n t) ≫ y := by
  have h₁ := (square_iff_tensor_map a x n s z).1 hs
  have h₂ := (square_iff_tensor_map b y n t z).1 ht
  rw [Category.assoc, htarget, h₁, Category.assoc, h₂,
    ← Category.assoc, ← comp_whiskerRight, hsource]

theorem finite_cells {J : Type u} [SmallCategory J]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    {A : Type u} [Finite A] (X Y : A → SSet.{u}) (n : A → ℕ)
    (D : A → J ⥤ SSet.{u}) (c : ∀ a, Cocone (D a)) (hc : ∀ a, IsColimit (c a))
    (hX : ∀ a, IsCardinalPresentable (X a ⊗ Δ[n a]) κ)
    {j k : J} (v : j ⟶ k) (p : ∀ a, X a ⟶ Y a)
    (s : ∀ a, ((ihom (X a)).obj ((D a).obj j)).obj (op ⦋n a⦌))
    (t : ∀ a, ((ihom (Y a)).obj ((D a).obj k)).obj (op ⦋n a⦌))
    (heq : ∀ a,
      (simplexHomEquiv (X a) ((D a).obj j) (n a) (s a) ≫ (D a).map v) ≫ (c a).ι.app k =
        (p a ▷ Δ[n a] ≫ simplexHomEquiv (Y a) ((D a).obj k) (n a) (t a)) ≫
          (c a).ι.app k) :
    ∃ (l : J) (w : k ⟶ l), ∀ a,
      Square (p a) ((D a).map (v ≫ w)) (s a)
        (((ihom (Y a)).map ((D a).map w)).app (op ⦋n a⦌) (t a)) := by
  let lhs := fun a ↦ simplexHomEquiv (X a) ((D a).obj j) (n a) (s a) ≫ (D a).map v
  let rhs := fun a ↦ p a ▷ Δ[n a] ≫
    simplexHomEquiv (Y a) ((D a).obj k) (n a) (t a)
  obtain ⟨l, w, hw⟩ := DaggerFiniteStageEquations.all_equations κ
    (fun a ↦ X a ⊗ Δ[n a]) D c hc hX lhs rhs heq
  refine ⟨l, w, fun a ↦ (square_iff_tensor_map _ _ _ _ _).2 ?_⟩
  simpa only [simplexHomEquiv_post, Functor.map_comp, Category.assoc] using hw a

end DaggerRectangularCellStageRefinements
