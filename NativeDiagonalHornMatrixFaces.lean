import NativeDiagonalHornMatrixUnit
import NativeBisimplicialBoxYoneda
import NativeBisimplicialBoxIso

/-! Original face boxes cover the matrix and determine its maps by diagonal restriction. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialDiagonal DaggerNativeDiagonalHornMatrix
open DaggerNativeDiagonalHornMatrixUnit DaggerNativeBisimplicialBoxYoneda
open DaggerNativeBisimplicialBoxIso DaggerNativePartialFaceUnionGeometry
universe u
namespace DaggerNativeDiagonalHornMatrixFaces
noncomputable section

def faceBox {n : ℕ} (k j : Fin (n + 1)) (hj : j ≠ k) :
    box (SSet.stdSimplex.face {j}ᶜ : SSet.{u}) (SSet.stdSimplex.face {j}ᶜ : SSet.{u}) ⟶
      hornMatrix n k where
  app h :=
    { app := fun v p ↦
        ⟨(⟨p.1.val, SSet.face_le_horn j k hj h p.1.property⟩, p.2.val), by
          apply (matrixRow_membership k h v _ _).mpr
          exact ⟨j, hj, (mem_codimFace j h p.1.val).mp p.1.property,
            (mem_codimFace j v p.2.val).mp p.2.property⟩⟩
      naturality := by
        intros
        funext p
        apply Subtype.ext
        rfl }
  naturality _ _ _ := by
    apply NatTrans.ext
    funext v p
    apply Subtype.ext
    rfl

theorem faceBox_cover {n : ℕ} (k : Fin (n + 1)) (h v : SimplexCategoryᵒᵖ)
    (p : (hornMatrix.{u} n k).obj h |>.obj v) :
    ∃ (j : Fin (n + 1)) (hj : j ≠ k)
      (a : (SSet.stdSimplex.face {j}ᶜ : SSet.{u}).obj h)
      (b : (SSet.stdSimplex.face {j}ᶜ : SSet.{u}).obj v),
      ((faceBox k j hj).app h).app v (a, b) = p := by
  obtain ⟨j, hj, ha, hb⟩ := (matrixRow_membership k h v p.val.1 p.val.2).mp p.property
  refine ⟨j, hj, ⟨p.val.1.val, (mem_codimFace j h _).mpr ha⟩,
    ⟨p.val.2, (mem_codimFace j v _).mpr hb⟩, ?_⟩
  apply Subtype.ext
  rfl

def matrixRestriction (n : ℕ) (k : Fin (n + 1)) (X : BiSSet.{u})
    (f : hornMatrix n k ⟶ X) :
    (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X :=
  diagonalHornUnit n k ≫ diagonalFunctor.map f

theorem faceBox_diagonal_square {n : ℕ} (k j : Fin (n + 2)) (hj : j ≠ k) :
    simplexDiagonalUnit.{u} n ≫ diagonalFunctor.map
        ((boxIso (SSet.stdSimplex.faceSingletonComplIso j)
          (SSet.stdSimplex.faceSingletonComplIso j)).hom ≫ faceBox k j hj) =
      (SSet.stdSimplex.faceSingletonComplIso j).hom ≫ SSet.horn.faceι k j hj ≫
        diagonalHornUnit (n + 1) k := by
  apply NatTrans.ext
  funext h a
  apply Subtype.ext
  rfl

theorem faceBox_restriction {n : ℕ} (k j : Fin (n + 2)) (hj : j ≠ k)
    (X : BiSSet.{u}) (f : hornMatrix (n + 1) k ⟶ X) :
    simplexRestriction n X
        ((boxIso (SSet.stdSimplex.faceSingletonComplIso j)
          (SSet.stdSimplex.faceSingletonComplIso j)).hom ≫ faceBox k j hj ≫ f) =
      (SSet.stdSimplex.faceSingletonComplIso j).hom ≫ SSet.horn.faceι k j hj ≫
        matrixRestriction (n + 1) k X f := by
  have hh := congrArg (fun t ↦ t ≫ diagonalFunctor.map f)
    (faceBox_diagonal_square k j hj)
  simpa only [simplexRestriction, matrixRestriction, diagonalFunctor.map_comp,
    Category.assoc] using hh

theorem matrixRestriction_injective (n : ℕ) (k : Fin (n + 1)) (X : BiSSet.{u}) :
    Function.Injective (matrixRestriction n k X) := by
  intro f g hfg
  cases n with
  | zero =>
    apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    obtain ⟨j, hj⟩ := missingFaces_nonempty k h p.val.1
    exact False.elim ((Finset.mem_filter.mp hj).2.1 (Fin.ext (by omega)))
  | succ n =>
    have hf : ∀ (j : Fin (n + 2)) (hj : j ≠ k), faceBox k j hj ≫ f =
        faceBox k j hj ≫ g := by
      intro j hj
      apply (cancel_epi (boxIso (SSet.stdSimplex.faceSingletonComplIso j)
        (SSet.stdSimplex.faceSingletonComplIso j)).hom).mp
      apply (simplexRestriction_bijective n X).injective
      rw [faceBox_restriction, faceBox_restriction, hfg]
    apply NatTrans.ext
    funext h
    apply NatTrans.ext
    funext v p
    obtain ⟨j, hj, a, b, hp⟩ := faceBox_cover k h v p
    have hh := congrFun (NatTrans.congr_app (NatTrans.congr_app (hf j hj) h) v) (a, b)
    change (f.app h).app v (((faceBox k j hj).app h).app v (a, b)) =
      (g.app h).app v (((faceBox k j hj).app h).app v (a, b)) at hh
    simpa only [hp] using hh

end
end DaggerNativeDiagonalHornMatrixFaces
