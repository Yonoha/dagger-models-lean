import NativeBisimplicialBoxHom
import NativeBisimplicialDiagonal

/-! Double Yoneda identifies the literal box and diagonal simplex mapping problems. -/
set_option autoImplicit false
open CategoryTheory CartesianMonoidalCategory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxHom DaggerNativeBisimplicialDiagonal
universe u
namespace DaggerNativeBisimplicialBoxYoneda
noncomputable section

def simplexBoxEquiv (m n : ℕ) (X : BiSSet.{u}) :
    (box (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) ≃
      (X.obj (op ⦋m⦌)).obj (op ⦋n⦌) :=
  (boxHomEquiv (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) X).trans
    ((Iso.homCongr (Iso.refl _) (horizontalSimplexIso X m)).trans SSet.yonedaEquiv)

theorem simplexBoxEquiv_value (m n : ℕ) (X : BiSSet.{u})
    (f : box (Δ[m] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) :
    simplexBoxEquiv m n X f = (f.app (op ⦋m⦌)).app (op ⦋n⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 _), SSet.stdSimplex.objEquiv.symm (𝟙 _)) := rfl

def simplexDiagonalUnit (n : ℕ) :
    (Δ[n] : SSet.{u}) ⟶ diagonalFunctor.obj (box (Δ[n] : SSet.{u}) Δ[n]) where
  app _ a := (a, a)
  naturality _ _ _ := rfl

def simplexRestriction (n : ℕ) (X : BiSSet.{u})
    (f : box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) :
    (Δ[n] : SSet.{u}) ⟶ diagonalFunctor.obj X :=
  simplexDiagonalUnit n ≫ diagonalFunctor.map f

def simplexDiagonalEquiv (n : ℕ) (X : BiSSet.{u}) :
    (box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) ≃
      ((Δ[n] : SSet.{u}) ⟶ diagonalFunctor.obj X) :=
  (simplexBoxEquiv n n X).trans
    (SSet.yonedaEquiv (X := diagonalFunctor.obj X) (n := ⦋n⦌)).symm

theorem simplexDiagonalEquiv_apply (n : ℕ) (X : BiSSet.{u})
    (f : box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) :
    simplexDiagonalEquiv n X f = simplexRestriction n X f := by
  apply SSet.yonedaEquiv.injective
  change (SSet.yonedaEquiv (X := diagonalFunctor.obj X) (n := ⦋n⦌))
    ((SSet.yonedaEquiv (X := diagonalFunctor.obj X) (n := ⦋n⦌)).symm
      (simplexBoxEquiv n n X f)) = _
  exact SSet.yonedaEquiv.apply_symm_apply _

theorem simplexRestriction_bijective (n : ℕ) (X : BiSSet.{u}) :
    Function.Bijective (simplexRestriction n X) := by
  have h : simplexRestriction n X = simplexDiagonalEquiv n X := by
    funext f
    exact (simplexDiagonalEquiv_apply n X f).symm
  rw [h]
  exact (simplexDiagonalEquiv n X).bijective

theorem simplexDiagonalUnit_natural {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    simplexDiagonalUnit.{u} m ≫
        diagonalFunctor.map (boxMap (SSet.stdSimplex.map α) (SSet.stdSimplex.map α)) =
      SSet.stdSimplex.map α ≫ simplexDiagonalUnit n := by
  apply NatTrans.ext
  rfl

theorem simplexRestriction_pre {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (X : BiSSet.{u})
    (f : box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) :
    simplexRestriction m X
        (boxMap (SSet.stdSimplex.map α) (SSet.stdSimplex.map α) ≫ f) =
      SSet.stdSimplex.map α ≫ simplexRestriction n X f := by
  simp only [simplexRestriction, diagonalFunctor.map_comp, ← Category.assoc,
    simplexDiagonalUnit_natural]

theorem simplexRestriction_post (n : ℕ) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (g : box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X) :
    simplexRestriction n Y (g ≫ f) =
      simplexRestriction n X g ≫ diagonalFunctor.map f := by
  simp only [simplexRestriction, diagonalFunctor.map_comp, Category.assoc]

def simplexExtension (n : ℕ) (X : BiSSet.{u})
    (a : (Δ[n] : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    box (Δ[n] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X :=
  (simplexDiagonalEquiv n X).symm a

theorem simplexExtension_restrict (n : ℕ) (X : BiSSet.{u})
    (a : (Δ[n] : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    simplexRestriction n X (simplexExtension n X a) = a := by
  rw [← simplexDiagonalEquiv_apply]
  exact (simplexDiagonalEquiv n X).apply_symm_apply a

theorem simplexExtension_natural {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (X : BiSSet.{u})
    (a : (Δ[n] : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    boxMap (SSet.stdSimplex.map α) (SSet.stdSimplex.map α) ≫ simplexExtension n X a =
      simplexExtension m X (SSet.stdSimplex.map α ≫ a) := by
  apply (simplexRestriction_bijective m X).injective
  rw [simplexRestriction_pre, simplexExtension_restrict, simplexExtension_restrict]

end
end DaggerNativeBisimplicialBoxYoneda
