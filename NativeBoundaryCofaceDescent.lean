import OriginalCofaceIntersectionAgreement
import TopCatModelCategory.SSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Descend actual maps on all native cofaces to the entire original boundary. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCofaceIntersectionAgreement
universe u
namespace DaggerNativeBoundaryCofaceDescent
noncomputable section

def diagram (n : ℕ) :
    SSet.Subcomplex.MulticoequalizerDiagram (SSet.boundary.{u} n)
      (fun i : Fin (n + 1) ↦ SSet.stdSimplex.face {i}ᶜ)
      (fun i j ↦ SSet.stdSimplex.face {i}ᶜ ⊓ SSet.stdSimplex.face {j}ᶜ) :=
  ⟨(SSet.boundary_eq_iSup n).symm, fun _ _ ↦ rfl⟩

def cofork {X : SSet.{u}} {n : ℕ} (μ : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X))
    (h : ∀ (i j : Fin (n + 2)), i < j →
      SSet.Subcomplex.homOfLE inf_le_left ≫
          ((SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μ i) =
        SSet.Subcomplex.homOfLE inf_le_right ≫
          ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫ μ j)) :
    Multicofork ((diagram.{u} (n + 1)).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun i ↦ (SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μ i)
    (fun ⟨⟨i,j⟩, hij⟩ ↦ h i j hij)

def desc {X : SSet.{u}} {n : ℕ} (μ : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X))
    (h : ∀ (i j : Fin (n + 2)), i < j →
      SSet.Subcomplex.homOfLE inf_le_left ≫
          ((SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μ i) =
        SSet.Subcomplex.homOfLE inf_le_right ≫
          ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫ μ j)) :
    (SSet.boundary (n + 1) : SSet.{u}) ⟶ X :=
  (diagram (n + 1)).isColimit'.desc (cofork μ h)

theorem desc_face {X : SSet.{u}} {n : ℕ}
    (μ : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X))
    (h : ∀ (i j : Fin (n + 2)), i < j →
      SSet.Subcomplex.homOfLE inf_le_left ≫
          ((SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μ i) =
        SSet.Subcomplex.homOfLE inf_le_right ≫
          ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫ μ j)) (i : Fin (n + 2)) :
    SSet.boundary.ι i ≫ desc μ h = μ i := by
  have hf := (diagram (n + 1)).isColimit'.fac (cofork μ h) (.right i)
  change SSet.Subcomplex.homOfLE (SSet.face_le_boundary i) ≫ desc μ h =
    (SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μ i at hf
  change ((SSet.stdSimplex.faceSingletonComplIso i).hom ≫
    SSet.Subcomplex.homOfLE (SSet.face_le_boundary i)) ≫ desc μ h = μ i
  rw [Category.assoc, hf, Iso.hom_inv_id_assoc]

theorem intersection_compatibility {X : SSet.{u}} {n : ℕ}
    (μ : Fin (n + 3) → ((Δ[n + 1] : SSet.{u}) ⟶ X))
    (h : ∀ (a b : Fin (n + 2)), a ≤ b →
      SSet.stdSimplex.δ a ≫ μ b.succ = SSet.stdSimplex.δ b ≫ μ a.castSucc)
    (i j : Fin (n + 3)) (hij : i < j) :
    SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μ i) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫ μ j) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin (n + 2), a.castSucc = i := by
    refine ⟨⟨i.val, by have hj := j.isLt; change i.val < j.val at hij; omega⟩, ?_⟩
    exact Fin.ext rfl
  obtain ⟨b, rfl⟩ : ∃ b : Fin (n + 2), b.succ = j := by
    refine ⟨⟨j.val - 1, by have hj := j.isLt; change a.val < j.val at hij; omega⟩, ?_⟩
    apply Fin.ext
    change j.val - 1 + 1 = j.val
    change a.val < j.val at hij
    omega
  have hab : a ≤ b := by
    change a.val ≤ b.val
    change a.val < b.val + 1 at hij
    omega
  exact intersection_agreement a b hab (μ a.castSucc) (μ b.succ) (h a b hab)

end
end DaggerNativeBoundaryCofaceDescent
