import ActualQRealizationFaceUnionGluing

/-! Finite unions of literal simplex faces with a common vertex have weak Q-realization. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open DaggerActualQRealizationFaceUnionGluing
universe u v

namespace DaggerActualQRealizationCommonVertexFaces

noncomputable section

/-- The actual union in the subcomplex lattice of the unchanged standard simplex. -/
def faceUnion {n : ℕ} {α : Type v} (s : Finset α)
    (f : α → Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex :=
  s.sup (fun j ↦ SSet.stdSimplex.face (f j))

/-- The singleton family is exactly its one literal face. -/
theorem faceUnion_singleton {n : ℕ} {α : Type v} (j : α)
    (f : α → Finset (Fin (n + 1))) :
    faceUnion.{u} ({j} : Finset α) f = SSet.stdSimplex.face.{u} (f j) := by
  classical
  exact Finset.sup_singleton

/-- Intersection with one literal face distributes over the entire finite union. -/
theorem face_inf_faceUnion {n : ℕ} {α : Type v} (S : Finset (Fin (n + 1)))
    (s : Finset α) (f : α → Finset (Fin (n + 1))) :
    SSet.stdSimplex.face.{u} S ⊓ faceUnion.{u} s f =
      faceUnion.{u} s (fun j ↦ S ⊓ f j) := by
  unfold faceUnion
  simp only [← SSet.stdSimplex.face_inter_face, Finset.sup_eq_iSup]
  ext q x
  simp only [CategoryTheory.Subfunctor.min_obj, SSet.Subcomplex.iSup_obj,
    Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hS, j, hj, hfj⟩
    exact ⟨j, hj, hS, hfj⟩
  · rintro ⟨j, hj, hS, hfj⟩
    exact ⟨hS, j, hj, hfj⟩

/-- Nonempty finite families of faces sharing a vertex are weakly contractible after realization. -/
theorem faceUnion_toUnit_GW {n : ℕ} {α : Type v} (s : Finset α)
    (f : α → Finset (Fin (n + 1))) (a : Fin (n + 1))
    (hs : s.Nonempty) (ha : ∀ j ∈ s, a ∈ f j) :
    GW (toUnit (realization.{u}.obj (faceUnion.{u} s f).toSSet)) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert j s hj ih =>
    have hfa : a ∈ f j := ha j (by simp)
    by_cases hS : s.Nonempty
    · have hV := ih f hS (fun k hk ↦ ha k (Finset.mem_insert_of_mem hk))
      have hU := face_toUnit_GW.{u} (f j) ⟨a, hfa⟩
      have hI : GW (toUnit (realization.{u}.obj
          (SSet.stdSimplex.face (f j) ⊓ faceUnion.{u} s f).toSSet)) := by
        rw [face_inf_faceUnion]
        apply ih (fun k ↦ f j ⊓ f k) hS
        intro k hk
        exact Finset.mem_inter.mpr ⟨hfa, ha k (Finset.mem_insert_of_mem hk)⟩
      rw [faceUnion, Finset.sup_insert]
      exact sup_toUnit_GW (SSet.stdSimplex.face (f j)) (faceUnion.{u} s f) hI hU hV
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst s
      rw [show insert j (∅ : Finset α) = {j} from rfl, faceUnion_singleton]
      exact face_toUnit_GW.{u} (f j) ⟨a, hfa⟩

end
end DaggerActualQRealizationCommonVertexFaces
