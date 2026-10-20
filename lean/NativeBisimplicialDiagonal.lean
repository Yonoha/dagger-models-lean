import NativeBisimplicialBox
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! The original diagonal uses native uncurrying and diagonal precomposition. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
universe u
namespace DaggerNativeBisimplicialDiagonal
noncomputable section

def diagonalFunctor : BiSSet.{u} ⥤ SSet.{u} :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ
    (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type u)).obj (Functor.diag SimplexCategoryᵒᵖ)

theorem diagonal_obj (X : BiSSet.{u}) (d : SimplexCategoryᵒᵖ) :
    (diagonalFunctor.obj X).obj d = (X.obj d).obj d := rfl

theorem diagonal_map_app {X Y : BiSSet.{u}} (f : X ⟶ Y) (d : SimplexCategoryᵒᵖ) :
    (diagonalFunctor.map f).app d = (f.app d).app d := rfl

def diagonalBoxIso (K A : SSet.{u}) : diagonalFunctor.obj (box K A) ≅ K ⊗ A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

theorem diagonal_boxMap {K L A B : SSet.{u}} (i : K ⟶ L) (j : A ⟶ B) :
    diagonalFunctor.map (boxMap i j) ≫ (diagonalBoxIso L B).hom =
      (diagonalBoxIso K A).hom ≫ (i ⊗ₘ j) := by
  apply NatTrans.ext
  rfl

def diagonalFlipIso (X : BiSSet.{u}) :
    diagonalFunctor.obj X.flip ≅ diagonalFunctor.obj X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro d e α
    exact (X.map α).naturality α)

instance diagonal_preservesLimits : PreservesLimits diagonalFunctor.{u} := by
  have hu : PreservesLimits (Functor.currying (C := SimplexCategoryᵒᵖ)
      (D := SimplexCategoryᵒᵖ) (E := Type u)).functor := inferInstance
  have : PreservesLimits (Functor.uncurry (C := SimplexCategoryᵒᵖ)
      (D := SimplexCategoryᵒᵖ) (E := Type u)) := hu
  have hw : PreservesLimits ((Functor.whiskeringLeft SimplexCategoryᵒᵖ
      (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) (Type u)).obj
        (Functor.diag SimplexCategoryᵒᵖ)) := inferInstance
  unfold diagonalFunctor
  exact comp_preservesLimits _ _

end
end DaggerNativeBisimplicialDiagonal
