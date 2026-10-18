import RigidificationCofPathFaces
import RigidificationCofSimplexRestriction

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

def missingFace (k : Fin (n + 2)) : Finset (Fin (n + 2)) := Finset.univ.erase k

theorem mem_missingFace (k i : Fin (n + 2)) : i ∈ missingFace k ↔ i ≠ k := by
  simp only [missingFace, Finset.mem_erase, Finset.mem_univ, and_true]

theorem missingFace_proper (k : Fin (n + 2)) : missingFace k ≠ Finset.univ := by
  intro h
  have hk : k ∈ missingFace k := by rw [h]; exact Finset.mem_univ _
  exact (mem_missingFace k k).mp hk rfl

theorem missingFace_zero (k : interior n) : (0 : Fin (n + 2)) ∈ missingFace k.val :=
  (mem_missingFace _ _).mpr (ne_of_lt k.property.1)

theorem missingFace_last (k : interior n) : Fin.last (n + 1) ∈ missingFace k.val :=
  (mem_missingFace _ _).mpr (ne_of_gt k.property.2)

theorem omitted_le_paths (k : Fin (n + 2)) (i j : Fin (n + 2)) :
    omitted (ULift.up i) (ULift.up j) (ULift.up k) ≤ pathsInFace.{u} (missingFace k) i j := by
  intro q γ h t x hx
  apply (mem_missingFace _ _).mpr
  intro e
  apply h t
  have he : x = ULift.up k := ULift.ext _ _ e
  exact he ▸ hx

def omittedEvaluation (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A) (k : interior n) :
    (extremeOmitted.{u} n k).toSSet ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))) :=
  SSet.Subcomplex.homOfLE (omitted_le_paths k.val 0 (Fin.last (n + 1))) ≫
    faceEvaluation a (missingFace k.val) ⟨0, missingFace_zero k⟩ (missingFace_proper k.val)
      0 (Fin.last (n + 1)) (missingFace_zero k) (missingFace_last k)

/-- All restrictions are full SSet maps into the SAME target, not only scalar vertices. -/
theorem evaluation_from_common (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    {i j : Fin (n + 2)} {U : (hom (ULift.up i) (ULift.up j)).Subcomplex}
    (s t : Finset (Fin (n + 2))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hps : s ≠ Finset.univ) (hpt : t ≠ Finset.univ) (hst : s ⊆ t)
    (hi : i ∈ s) (hj : j ∈ s) (hUs : U ≤ pathsInFace s i j)
    (hUt : U ≤ pathsInFace t i j) :
    SSet.Subcomplex.homOfLE hUt ≫ faceEvaluation a t ht hpt i j (hst hi) (hst hj) =
      SSet.Subcomplex.homOfLE hUs ≫ faceEvaluation a s hs hps i j hi hj := by
  have h := faceEvaluation_restrict a s t hs ht hps hpt hst i j hi hj
  rw [← h, ← Category.assoc, SSet.Subcomplex.homOfLE_comp]

/-- Omit/omit agreement on the ENTIRE actual intersection. -/
theorem omitted_overlap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k l : interior n) :
    SSet.Subcomplex.homOfLE (inf_le_left : extremeOmitted n k ⊓ extremeOmitted n l ≤ _)
        ≫ omittedEvaluation a k =
      SSet.Subcomplex.homOfLE (inf_le_right : extremeOmitted n k ⊓ extremeOmitted n l ≤ _)
        ≫ omittedEvaluation a l := by
  let s := missingFace k.val ∩ missingFace l.val
  have hi : (0 : Fin (n + 2)) ∈ s :=
    Finset.mem_inter.mpr ⟨missingFace_zero k, missingFace_zero l⟩
  have hj : Fin.last (n + 1) ∈ s :=
    Finset.mem_inter.mpr ⟨missingFace_last k, missingFace_last l⟩
  have hs : s.Nonempty := ⟨0, hi⟩
  have hp : s ≠ Finset.univ := by
    intro h
    apply missingFace_proper k.val
    apply Finset.eq_univ_of_forall
    intro x
    apply Finset.inter_subset_left (s₂ := missingFace l.val)
    change x ∈ s
    rw [h]
    exact Finset.mem_univ _
  have hUs : extremeOmitted.{u} n k ⊓ extremeOmitted n l ≤
      pathsInFace s 0 (Fin.last (n + 1)) := by
    intro q γ h t x hx
    have hk' := omitted_le_paths k.val 0 (Fin.last (n + 1)) q h.1
    have hl' := omitted_le_paths l.val 0 (Fin.last (n + 1)) q h.2
    exact Finset.mem_inter.mpr ⟨hk' t x hx, hl' t x hx⟩
  unfold omittedEvaluation
  rw [← Category.assoc, SSet.Subcomplex.homOfLE_comp,
    ← Category.assoc, SSet.Subcomplex.homOfLE_comp]
  rw [evaluation_from_common a s (missingFace k.val) hs ⟨0, missingFace_zero k⟩ hp
      (missingFace_proper k.val) Finset.inter_subset_left hi hj hUs,
    evaluation_from_common a s (missingFace l.val) hs ⟨0, missingFace_zero l⟩ hp
      (missingFace_proper l.val) Finset.inter_subset_right hi hj hUs]

end

end DaggerOrdinaryRigidificationCof.BoundaryData
