import NativeDiagonalHornMatrixFaces
import NativeFaceBoxDiagonalEquivalence

/-! Extend original diagonal horn data by gluing its actual overlapping face boxes. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialDiagonal DaggerNativeDiagonalHornMatrix
open DaggerNativeDiagonalHornMatrixUnit DaggerNativeDiagonalHornMatrixFaces
open DaggerNativePartialFaceUnionGeometry DaggerNativeFaceBoxDiagonalEquivalence
universe u
namespace DaggerNativeDiagonalHornMatrixExtension
noncomputable section

def faceData {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (j : Fin (n + 1)) (hj : j ≠ k) :
    box (SSet.stdSimplex.face {j}ᶜ : SSet.{u}) (SSet.stdSimplex.face {j}ᶜ : SSet.{u}) ⟶ X :=
  faceBoxExtension {j}ᶜ X (SSet.horn.faceι k j hj ≫ a)

theorem faceData_restrict {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (j : Fin (n + 1)) (hj : j ≠ k) :
    boxRestriction _ X (faceData k X a j hj) = SSet.horn.faceι k j hj ≫ a :=
  faceBoxExtension_restrict _ X _

def overlapLeft {n : ℕ} (j l : Fin (n + 1)) :
    (SSet.stdSimplex.face ({j}ᶜ ⊓ {l}ᶜ) : SSet.{u}) ⟶
      (SSet.stdSimplex.face {j}ᶜ : SSet.{u}) :=
  SSet.Subcomplex.homOfLE ((SSet.stdSimplex.face_le_face_iff _ _).mpr inf_le_left)

def overlapRight {n : ℕ} (j l : Fin (n + 1)) :
    (SSet.stdSimplex.face ({j}ᶜ ⊓ {l}ᶜ) : SSet.{u}) ⟶
      (SSet.stdSimplex.face {l}ᶜ : SSet.{u}) :=
  SSet.Subcomplex.homOfLE ((SSet.stdSimplex.face_le_face_iff _ _).mpr inf_le_right)

theorem faceData_overlap {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (j l : Fin (n + 1)) (hj : j ≠ k) (hl : l ≠ k) :
    boxMap (overlapLeft j l) (overlapLeft j l) ≫ faceData k X a j hj =
      boxMap (overlapRight j l) (overlapRight j l) ≫ faceData k X a l hl := by
  apply (faceBoxRestriction_bijective ({j}ᶜ ⊓ {l}ᶜ) X).injective
  rw [boxRestriction_pre, boxRestriction_pre, faceData_restrict, faceData_restrict]
  have hh : overlapLeft j l ≫ SSet.horn.faceι k j hj =
      overlapRight j l ≫ SSet.horn.faceι k l hl := by
    apply NatTrans.ext
    rfl
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ a) hh

def overlapPoint {n : ℕ} (j l : Fin (n + 1)) (h : SimplexCategoryᵒᵖ)
    (x : (Δ[n] : SSet.{u}).obj h)
    (hj : x ∈ (SSet.stdSimplex.face {j}ᶜ).obj h)
    (hl : x ∈ (SSet.stdSimplex.face {l}ᶜ).obj h) :
    (SSet.stdSimplex.face ({j}ᶜ ⊓ {l}ᶜ) : SSet.{u}).obj h :=
  ⟨x, by rw [← SSet.stdSimplex.face_inter_face]; exact ⟨hj, hl⟩⟩

theorem faceData_point_eq {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (j l : Fin (n + 1)) (hj : j ≠ k) (hl : l ≠ k)
    (h v : SimplexCategoryᵒᵖ) (x : (Δ[n] : SSet.{u}).obj h)
    (y : (Δ[n] : SSet.{u}).obj v)
    (hxj : x ∈ (SSet.stdSimplex.face {j}ᶜ).obj h)
    (hxl : x ∈ (SSet.stdSimplex.face {l}ᶜ).obj h)
    (hyj : y ∈ (SSet.stdSimplex.face {j}ᶜ).obj v)
    (hyl : y ∈ (SSet.stdSimplex.face {l}ᶜ).obj v) :
    ((faceData k X a j hj).app h).app v (⟨x, hxj⟩, ⟨y, hyj⟩) =
      ((faceData k X a l hl).app h).app v (⟨x, hxl⟩, ⟨y, hyl⟩) :=
  congrFun (NatTrans.congr_app (NatTrans.congr_app (faceData_overlap k X a j l hj hl) h) v)
    (overlapPoint j l h x hxj hxl, overlapPoint j l v y hyj hyl)

def chosenFace {n : ℕ} (k : Fin (n + 1)) (h v : SimplexCategoryᵒᵖ)
    (p : ((hornMatrix.{u} n k).obj h).obj v) : Fin (n + 1) :=
  Classical.choose ((matrixRow_membership k h v p.val.1 p.val.2).mp p.property)

theorem chosenFace_spec {n : ℕ} (k : Fin (n + 1)) (h v : SimplexCategoryᵒᵖ)
    (p : ((hornMatrix.{u} n k).obj h).obj v) :
    chosenFace k h v p ≠ k ∧
      p.val.1.val ∈ (SSet.stdSimplex.face {chosenFace k h v p}ᶜ).obj h ∧
      p.val.2 ∈ (SSet.stdSimplex.face {chosenFace k h v p}ᶜ).obj v := by
  have hs := Classical.choose_spec
    ((matrixRow_membership k h v p.val.1 p.val.2).mp p.property)
  exact ⟨hs.1, (mem_codimFace _ h _).mpr hs.2.1, (mem_codimFace _ v _).mpr hs.2.2⟩

def matrixValue {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (h v : SimplexCategoryᵒᵖ) (p : ((hornMatrix n k).obj h).obj v) :
    (X.obj h).obj v :=
  ((faceData k X a (chosenFace k h v p) (chosenFace_spec k h v p).1).app h).app v
    (⟨p.val.1.val, (chosenFace_spec k h v p).2.1⟩,
      ⟨p.val.2, (chosenFace_spec k h v p).2.2⟩)

theorem matrixValue_on_face {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X)
    (j : Fin (n + 1)) (hj : j ≠ k) (h v : SimplexCategoryᵒᵖ)
    (x : (SSet.stdSimplex.face {j}ᶜ : SSet.{u}).obj h)
    (y : (SSet.stdSimplex.face {j}ᶜ : SSet.{u}).obj v) :
    matrixValue k X a h v (((faceBox k j hj).app h).app v (x, y)) =
      ((faceData k X a j hj).app h).app v (x, y) := by
  let p := ((faceBox k j hj).app h).app v (x, y)
  exact faceData_point_eq k X a (chosenFace k h v p) j (chosenFace_spec k h v p).1 hj
    h v x.val y.val (chosenFace_spec k h v p).2.1 x.property
      (chosenFace_spec k h v p).2.2 y.property

def matrixExtension {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X) : hornMatrix n k ⟶ X where
  app h :=
    { app := matrixValue k X a h
      naturality := by
        intro v w β
        funext p
        obtain ⟨j, hj, x, y, rfl⟩ := faceBox_cover k h v p
        change matrixValue k X a h w
            (((faceBox k j hj).app h).app w (x, (SSet.stdSimplex.face {j}ᶜ).toSSet.map β y)) =
          (X.obj h).map β (matrixValue k X a h v (((faceBox k j hj).app h).app v (x, y)))
        rw [matrixValue_on_face, matrixValue_on_face]
        exact congrFun ((faceData k X a j hj).app h |>.naturality β) (x, y) }
  naturality h l α := by
    apply NatTrans.ext
    funext v p
    obtain ⟨j, hj, x, y, rfl⟩ := faceBox_cover k h v p
    change matrixValue k X a l v
        (((faceBox k j hj).app l).app v ((SSet.stdSimplex.face {j}ᶜ).toSSet.map α x, y)) =
      (X.map α).app v
        (matrixValue k X a h v (((faceBox k j hj).app h).app v (x, y)))
    rw [matrixValue_on_face, matrixValue_on_face]
    exact congrFun (NatTrans.congr_app ((faceData k X a j hj).naturality α) v) (x, y)

theorem matrixExtension_restrict {n : ℕ} (k : Fin (n + 1)) (X : BiSSet.{u})
    (a : (SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    matrixRestriction n k X (matrixExtension k X a) = a := by
  apply NatTrans.ext
  funext h x
  obtain ⟨j, hj⟩ := missingFaces_nonempty k h x
  have hs := (Finset.mem_filter.mp hj).2
  let y : (SSet.stdSimplex.face {j}ᶜ : SSet.{u}).obj h :=
    ⟨x.val, (mem_codimFace j h x.val).mpr hs.2⟩
  have hp : (diagonalHornUnit n k).app h x =
      ((faceBox k j hs.1).app h).app h (y, y) := by
    apply Subtype.ext
    rfl
  change matrixValue k X a h h ((diagonalHornUnit n k).app h x) = a.app h x
  rw [hp, matrixValue_on_face]
  exact congrFun (NatTrans.congr_app (faceData_restrict k X a j hs.1) h) y

theorem matrixRestriction_bijective (n : ℕ) (k : Fin (n + 1)) (X : BiSSet.{u}) :
    Function.Bijective (matrixRestriction n k X) :=
  ⟨matrixRestriction_injective n k X, fun a ↦ ⟨matrixExtension k X a,
    matrixExtension_restrict k X a⟩⟩

def matrixHomEquiv (n : ℕ) (k : Fin (n + 1)) (X : BiSSet.{u}) :
    (hornMatrix n k ⟶ X) ≃ ((SSet.horn n k : SSet.{u}) ⟶ diagonalFunctor.obj X) :=
  Equiv.ofBijective _ (matrixRestriction_bijective n k X)

end
end DaggerNativeDiagonalHornMatrixExtension
