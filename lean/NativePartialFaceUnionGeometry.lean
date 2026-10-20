import NativeSubcomplexAttachmentPushout
import NativeHornMissingFaceGeometry

/-! Actual finite unions of codimension-one simplex faces and their exact attachment squares. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
universe u
namespace DaggerNativePartialFaceUnionGeometry
noncomputable section

def faceUnion {n : ℕ} (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  S.sup (fun j ↦ SSet.stdSimplex.face {j}ᶜ)

theorem mem_codimFace {n : ℕ} (j : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (x : (Δ[n] : SSet.{u}).obj d) :
    x ∈ (SSet.stdSimplex.face {j}ᶜ).obj d ↔
      ∀ r, SSet.stdSimplex.asOrderHom x r ≠ j := by
  cases d with
  | op d =>
    induction d using SimplexCategory.rec with
    | h m =>
      exact (SSet.stdSimplex.mem_face_iff {j}ᶜ x).trans (by
        simp only [Finset.mem_compl, Finset.mem_singleton]
        rfl)

theorem faceUnion_empty (n : ℕ) : faceUnion (∅ : Finset (Fin (n + 1))) =
    (⊥ : (Δ[n] : SSet.{u}).Subcomplex) := Finset.sup_empty

theorem faceUnion_insert {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    faceUnion (insert i S) = faceUnion S ⊔ SSet.stdSimplex.face {i}ᶜ := by
  exact (Finset.sup_insert (f := fun j ↦ SSet.stdSimplex.face {j}ᶜ)).trans (sup_comm _ _)

theorem mem_faceUnion {n : ℕ} (S : Finset (Fin (n + 1))) (d : SimplexCategoryᵒᵖ)
    (x : (Δ[n] : SSet.{u}).obj d) :
    x ∈ (faceUnion S).obj d ↔
      ∃ j ∈ S, ∀ r, SSet.stdSimplex.asOrderHom x r ≠ j := by
  induction S using Finset.induction_on with
  | empty =>
    rw [faceUnion_empty]
    change False ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false]
  | @insert j S hj ih =>
    rw [faceUnion_insert]
    change (x ∈ (faceUnion S).obj d ∨ x ∈ (SSet.stdSimplex.face {j}ᶜ).obj d) ↔ _
    rw [ih, mem_codimFace]
    simp only [Finset.mem_insert]
    aesop

theorem faceUnion_le_horn {n : ℕ} (S : Finset (Fin (n + 1))) (k : Fin (n + 1))
    (hk : k ∉ S) : faceUnion.{u} S ≤ SSet.horn n k := by
  apply Finset.sup_le
  intro j hj
  exact SSet.face_le_horn j k (fun h ↦ hk (h ▸ hj))

def faceIndices {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2)) :
    Finset (Fin (n + 1)) := Finset.univ.filter (fun j ↦ i.succAbove j ∈ S)

theorem faceUnion_preimage_face {n : ℕ} (S : Finset (Fin (n + 2))) (i : Fin (n + 2))
    (hi : i ∉ S) : (faceUnion.{u} S).preimage (SSet.stdSimplex.δ i) =
      faceUnion (faceIndices S i) := by
  ext d x
  change (SSet.stdSimplex.δ i).app d x ∈ (faceUnion S).obj d ↔ _
  rw [mem_faceUnion, mem_faceUnion]
  constructor
  · rintro ⟨j, hj, hx⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (show j ≠ i from fun h ↦ hi (h ▸ hj))
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk ▸ hj⟩, ?_⟩
    intro r hr
    apply hx r
    change i.succAbove (SSet.stdSimplex.asOrderHom x r) = j
    rw [hr, hk]
  · rintro ⟨k, hk, hx⟩
    refine ⟨i.succAbove k, (Finset.mem_filter.mp hk).2, ?_⟩
    intro r hr
    apply hx r
    exact Fin.succAbove_right_injective hr

theorem faceUnion_attachment_isPushout {n : ℕ} (S : Finset (Fin (n + 2)))
    (i : Fin (n + 2)) :
    IsPushout ((faceUnion.{u} S).fromPreimage (SSet.stdSimplex.δ i))
      ((faceUnion S).preimage (SSet.stdSimplex.δ i)).ι
      (SSet.Subcomplex.homOfLE (show faceUnion S ≤ faceUnion (insert i S) from
        faceUnion_insert S i ▸ le_sup_left))
      (SSet.Subcomplex.lift (SSet.stdSimplex.δ i) (show
        SSet.Subcomplex.range (SSet.stdSimplex.δ i) ≤ faceUnion (insert i S) from by
        rw [SSet.stdSimplex.range_δ, faceUnion_insert]
        exact le_sup_right)) := by
  apply DaggerNativeSubcomplexAttachmentPushout.attachment_isPushout
  rw [SSet.stdSimplex.range_δ, faceUnion_insert]

end
end DaggerNativePartialFaceUnionGeometry
