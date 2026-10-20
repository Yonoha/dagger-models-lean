import OriginalZeroJoinStandardTransposition
import OriginalCofaceIntersectionAgreement

/-!
# Whole-face agreement for the native inverse cone construction

Original standard cofaces into a subcomplex retain their original ambient
operators. Their common-face relation transfers through the verified native
vertex-join transposition to agreement on the entire successor face overlap.
All dimension casts are explicit original ordinal casts.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalCofaceIntersectionAgreement
open DaggerOriginalZeroJoinStandardTransposition

universe u

namespace DaggerOriginalTransposedBoundaryFaceAgreement

noncomputable section

/-- The original standard coface into an actual subcomplex containing that whole face. -/
def boundaryFaceInclusion {n : ℕ} (A : (Δ[n + 1] : SSet.{u}).Subcomplex)
    (i : Fin (n + 2)) (hi : SSet.stdSimplex.face {i}ᶜ ≤ A) : (Δ[n] : SSet.{u}) ⟶ A :=
  (SSet.stdSimplex.faceSingletonComplIso i).hom ≫ SSet.Subcomplex.homOfLE hi

/-- Its ambient composite is the same original standard coface. -/
theorem boundaryFaceInclusion_comp {n : ℕ} (A : (Δ[n + 1] : SSet.{u}).Subcomplex)
    (i : Fin (n + 2)) (hi : SSet.stdSimplex.face {i}ᶜ ≤ A) :
    boundaryFaceInclusion A i hi ≫ A.ι = SSet.stdSimplex.δ i := by
  rw [boundaryFaceInclusion, Category.assoc, SSet.Subcomplex.homOfLE_ι,
    SSet.stdSimplex.faceSingletonComplIso_hom_ι]

/-- Original boundary cofaces satisfy the exact original common-face equation. -/
theorem boundaryFaceInclusion_common_face {n : ℕ}
    (A : (Δ[n + 2] : SSet.{u}).Subcomplex) (a b : Fin (n + 2)) (hab : a ≤ b)
    (ha : SSet.stdSimplex.face {a.castSucc}ᶜ ≤ A)
    (hb : SSet.stdSimplex.face {b.succ}ᶜ ≤ A) :
    SSet.stdSimplex.δ a ≫ boundaryFaceInclusion A b.succ hb =
      SSet.stdSimplex.δ b ≫ boundaryFaceInclusion A a.castSucc ha := by
  apply (cancel_mono A.ι).mp
  rw [Category.assoc, boundaryFaceInclusion_comp, Category.assoc, boundaryFaceInclusion_comp]
  exact (SSet.stdSimplex.map_comp _ _).symm.trans
    ((congrArg SSet.stdSimplex.map (SimplexCategory.δ_comp_δ hab)).trans
      (SSet.stdSimplex.map_comp _ _))

/-- Transposition of the original boundary data agrees on every whole successor face overlap.
-/
theorem transposed_boundary_face_agreement {X : SSet.{u}} {n : ℕ}
    (A : (Δ[n + 2] : SSet.{u}).Subcomplex) (a b : Fin (n + 2)) (hab : a ≤ b)
    (ha : SSet.stdSimplex.face {a.castSucc}ᶜ ≤ A)
    (hb : SSet.stdSimplex.face {b.succ}ᶜ ≤ A) (t : (A : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso a.castSucc.succ).inv ≫
          zeroJoinStandardTranspose (n + 1) (boundaryFaceInclusion A a.castSucc ha ≫ t)) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso b.succ.succ).inv ≫
          zeroJoinStandardTranspose (n + 1) (boundaryFaceInclusion A b.succ hb ≫ t)) := by
  have w := congrArg (fun f ↦ f ≫ t) (boundaryFaceInclusion_common_face A a b hab ha hb)
  dsimp only at w
  simp only [Category.assoc] at w
  have h := intersection_agreement (n := n + 1) a.succ b.succ
    (by change a.val + 1 ≤ b.val + 1; change a.val ≤ b.val at hab; omega)
    (zeroJoinStandardTranspose (n + 1) (boundaryFaceInclusion A a.castSucc ha ≫ t))
    (zeroJoinStandardTranspose (n + 1) (boundaryFaceInclusion A b.succ hb ≫ t))
    (zeroJoinStandardTranspose_common_face n a b _ _ w)
  have hi : a.succ.castSucc = a.castSucc.succ := Fin.ext rfl
  rw [hi] at h
  exact h

/-- Every strictly ordered original pair gives that whole-overlap agreement, retaining the
original face indices rather than a selected common-face representation. -/
theorem transposed_boundary_face_agreement_of_lt {X : SSet.{u}} (N : ℕ) (hN : 0 < N)
    (A : (Δ[N + 1] : SSet.{u}).Subcomplex) (j l : Fin (N + 2)) (hjl : j < l)
    (hj : SSet.stdSimplex.face {j}ᶜ ≤ A) (hl : SSet.stdSimplex.face {l}ᶜ ≤ A)
    (t : (A : SSet.{u}) ⟶ joinedPresheaf ⦋0⦌ X) :
    SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso j.succ).inv ≫
          zeroJoinStandardTranspose N (boundaryFaceInclusion A j hj ≫ t)) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso l.succ).inv ≫
          zeroJoinStandardTranspose N (boundaryFaceInclusion A l hl ≫ t)) := by
  cases N with
  | zero => omega
  | succ n =>
    have hjv : j.val < l.val := hjl
    have hlj := l.isLt
    obtain ⟨a, ha⟩ : ∃ a : Fin (n + 2), a.castSucc = j :=
      ⟨⟨j.val, by omega⟩, Fin.ext rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : Fin (n + 2), b.succ = l :=
      ⟨⟨l.val - 1, by omega⟩, Fin.ext (by change l.val - 1 + 1 = l.val; omega)⟩
    have hav := congrArg Fin.val ha
    have hbv := congrArg Fin.val hb
    have hab : a ≤ b := by
      change a.val = j.val at hav
      change b.val + 1 = l.val at hbv
      change a.val ≤ b.val
      omega
    subst j
    subst l
    exact transposed_boundary_face_agreement A a b hab hj hl t


/-- Transport whole-face agreement through the exact original standard-dimension equality. -/
theorem face_intersection_agreement_cast {X : SSet.{u}} {m n : ℕ} (h : m = n)
    (i j : Fin (n + 2)) (μi μj : (Δ[n] : SSet.{u}) ⟶ X)
    (w : SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso i).inv ≫ μi) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫ μj)) :
    SSet.Subcomplex.homOfLE inf_le_left ≫
        ((SSet.stdSimplex.faceSingletonComplIso
          (Fin.cast (congrArg (fun v ↦ v + 2) h.symm) i)).inv ≫
            (SSet.stdSimplex.map (eqToHom (congrArg SimplexCategory.mk h)) ≫ μi)) =
      SSet.Subcomplex.homOfLE inf_le_right ≫
        ((SSet.stdSimplex.faceSingletonComplIso
          (Fin.cast (congrArg (fun v ↦ v + 2) h.symm) j)).inv ≫
            (SSet.stdSimplex.map (eqToHom (congrArg SimplexCategory.mk h)) ≫ μj)) := by
  subst m
  simpa only [eqToHom_refl, Functor.map_id, Category.id_comp, Fin.cast_refl] using w

end

end DaggerOriginalTransposedBoundaryFaceAgreement
