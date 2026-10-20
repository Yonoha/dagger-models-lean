import NativeEndomorphismSimplexMaps
import FiniteStageEquations

/-!
# Actual internal-Hom cell squares become strict at a later stage

The complete tensor source is assumed cardinal-presentable. A finite standard
simplex parameter alone does not imply presentability of the whole source.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeEndomorphismCellSquares DaggerNativeEndomorphismSimplexMaps
universe u
namespace DaggerEndomorphismCellStageEquations

theorem equation_after_colimit {X Y Z : SSet.{u}} {n : ℕ} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ((ihom X).obj X).obj (op ⦋n⦌))
    (y : ((ihom Y).obj Y).obj (op ⦋n⦌))
    (z : ((ihom Z).obj Z).obj (op ⦋n⦌))
    (hab : CellSquare (a ≫ b) x z) (hb : CellSquare b y z) :
    (simplexHomEquiv X X n x ≫ a) ≫ b =
      (a ▷ Δ[n] ≫ simplexHomEquiv Y Y n y) ≫ b := by
  have h₁ := (cellSquare_iff_tensor_map_square (a ≫ b) n x z).1 hab
  have h₂ := (cellSquare_iff_tensor_map_square b n y z).1 hb
  simpa only [Category.assoc, comp_whiskerRight, ← h₂] using h₁

theorem square_after_stage {X Y Z : SSet.{u}} {n : ℕ} (a : X ⟶ Y) (b : Y ⟶ Z)
    (x : ((ihom X).obj X).obj (op ⦋n⦌))
    (y : ((ihom Y).obj Y).obj (op ⦋n⦌))
    (z : ((ihom Z).obj Z).obj (op ⦋n⦌))
    (heq : (simplexHomEquiv X X n x ≫ a) ≫ b =
      (a ▷ Δ[n] ≫ simplexHomEquiv Y Y n y) ≫ b)
    (hb : CellSquare b y z) : CellSquare (a ≫ b) x z := by
  apply (cellSquare_iff_tensor_map_square (a ≫ b) n x z).2
  have h₂ := (cellSquare_iff_tensor_map_square b n y z).1 hb
  simpa only [Category.assoc, comp_whiskerRight, ← h₂] using heq

theorem finite_cell_squares {J : Type u} [SmallCategory J]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    {A : Type u} [Finite A] (X : A → SSet.{u}) (n : A → ℕ)
    (D : A → J ⥤ SSet.{u}) (c : ∀ a, Cocone (D a))
    (hc : ∀ a, IsColimit (c a))
    (hX : ∀ a, IsCardinalPresentable (X a ⊗ Δ[n a]) κ)
    (x : ∀ a, ((ihom (X a)).obj (X a)).obj (op ⦋n a⦌))
    (s : ∀ a j, ((ihom ((D a).obj j)).obj ((D a).obj j)).obj (op ⦋n a⦌))
    (z : ∀ a, ((ihom (c a).pt).obj (c a).pt).obj (op ⦋n a⦌))
    (hleg : ∀ a j, CellSquare ((c a).ι.app j) (s a j) (z a))
    (hstage : ∀ a {i j} (f : i ⟶ j), CellSquare ((D a).map f) (s a i) (s a j))
    {i : J} (f : ∀ a, X a ⟶ (D a).obj i)
    (hf : ∀ a, CellSquare (f a ≫ (c a).ι.app i) (x a) (z a)) :
    ∃ (j : J) (t : i ⟶ j), ∀ a,
      CellSquare (f a ≫ (D a).map t) (x a) (s a j) := by
  let K := fun a ↦ X a ⊗ Δ[n a]
  let lhs := fun a ↦ simplexHomEquiv (X a) (X a) (n a) (x a) ≫ f a
  let rhs := fun a ↦ f a ▷ Δ[n a] ≫
    simplexHomEquiv ((D a).obj i) ((D a).obj i) (n a) (s a i)
  obtain ⟨j, t, ht⟩ := DaggerFiniteStageEquations.all_equations κ K D c hc hX lhs rhs
    (fun a ↦ equation_after_colimit (f a) ((c a).ι.app i) (x a) (s a i) (z a)
      (hf a) (hleg a i))
  exact ⟨j, t, fun a ↦ square_after_stage (f a) ((D a).map t)
    (x a) (s a i) (s a j) (ht a) (hstage a t)⟩

end DaggerEndomorphismCellStageEquations
