import NativeEndomorphismCellSquares

/-!
# Full internal-Hom simplices as maps with finite standard-simplex parameters

The Yoneda equivalence and the actual closed adjunction identify every simplex,
including all four inverse edges and four cancellation triangles. Strict cell
squares are exactly strict ordinary map squares under this equivalence.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerNativeEndomorphismCellSquares
universe u
namespace DaggerNativeEndomorphismSimplexMaps
noncomputable section

def simplexHomEquiv (A B : SSet.{u}) (n : ℕ) :
    ((ihom A).obj B).obj (op ⦋n⦌) ≃ (A ⊗ Δ[n] ⟶ B) :=
  SSet.yonedaEquiv.symm.trans ((ihom.adjunction A).homEquiv Δ[n] B).symm

theorem yoneda_symm_map {X Y : SSet.{u}} {n : ℕ} (f : X ⟶ Y) (s : X.obj (op ⦋n⦌)) :
    SSet.yonedaEquiv.symm (f.app (op ⦋n⦌) s) = SSet.yonedaEquiv.symm s ≫ f := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem simplexHomEquiv_post (A : SSet.{u}) {B Z : SSet.{u}} (f : B ⟶ Z) (n : ℕ)
    (s : ((ihom A).obj B).obj (op ⦋n⦌)) :
    simplexHomEquiv A Z n (((ihom A).map f).app (op ⦋n⦌) s) =
      simplexHomEquiv A B n s ≫ f := by
  change MonoidalClosed.uncurry
      (SSet.yonedaEquiv.symm (((ihom A).map f).app (op ⦋n⦌) s)) =
    MonoidalClosed.uncurry (SSet.yonedaEquiv.symm s) ≫ f
  rw [yoneda_symm_map, MonoidalClosed.uncurry_natural_right]

theorem simplexHomEquiv_pre {A B : SSet.{u}} (f : A ⟶ B) (Z : SSet.{u}) (n : ℕ)
    (s : ((ihom B).obj Z).obj (op ⦋n⦌)) :
    simplexHomEquiv A Z n (((MonoidalClosed.pre f).app Z).app (op ⦋n⦌) s) =
      f ▷ Δ[n] ≫ simplexHomEquiv B Z n s := by
  change MonoidalClosed.uncurry
      (SSet.yonedaEquiv.symm (((MonoidalClosed.pre f).app Z).app (op ⦋n⦌) s)) =
    f ▷ Δ[n] ≫ MonoidalClosed.uncurry (SSet.yonedaEquiv.symm s)
  rw [yoneda_symm_map, MonoidalClosed.uncurry_pre_app]

theorem cellSquare_iff_tensor_map_square {X Y : SSet.{u}} (a : X ⟶ Y) (n : ℕ)
    (x : ((ihom X).obj X).obj (op ⦋n⦌)) (y : ((ihom Y).obj Y).obj (op ⦋n⦌)) :
    CellSquare a x y ↔
      simplexHomEquiv X X n x ≫ a = a ▷ Δ[n] ≫ simplexHomEquiv Y Y n y := by
  constructor
  · intro h
    have hh := congrArg (simplexHomEquiv X Y n) h
    simpa only [simplexHomEquiv_post, simplexHomEquiv_pre] using hh
  · intro h
    apply (simplexHomEquiv X Y n).injective
    simpa only [simplexHomEquiv_post, simplexHomEquiv_pre] using h

end
end DaggerNativeEndomorphismSimplexMaps
