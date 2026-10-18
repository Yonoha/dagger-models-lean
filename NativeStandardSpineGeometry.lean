import NativeStandardSpineInner

/-! The exact transported standard spine is the union of its original successive edges and vertices.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeStandardSpineInner
universe u
namespace DaggerNativeStandardSpineGeometry
noncomputable section

def vertices (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i : Fin (n + 1), SSet.stdSimplex.face {i}

def edges (n : ℕ) : (Δ[n] : SSet.{u}).Subcomplex :=
  ⨆ i : Fin n, SSet.stdSimplex.face {i.castSucc, i.succ}

theorem vertexFace_le {n : ℕ} (i : Fin (n + 1)) :
    SSet.stdSimplex.face.{u} {i} ≤ spine n := by
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      rw [mem_spine_iff]
      rw [SSet.stdSimplex.mem_face_iff] at hc
      simp only [Finset.mem_singleton] at hc
      change ∀ j, SSet.stdSimplex.asOrderHom c j = i at hc
      rw [hc (Fin.last d), hc 0]
      omega

theorem edgeFace_le {n : ℕ} (i : Fin n) :
    SSet.stdSimplex.face.{u} {i.castSucc, i.succ} ≤ spine n := by
  intro q c hc
  induction q using Opposite.rec with | op q =>
    induction q using SimplexCategory.rec with | h d =>
      rw [mem_spine_iff]
      rw [SSet.stdSimplex.mem_face_iff] at hc
      change ∀ j, SSet.stdSimplex.asOrderHom c j ∈
        ({i.castSucc, i.succ} : Finset (Fin (n + 1))) at hc
      have h0 := hc 0
      have h1 := hc (Fin.last d)
      simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] <;>
        simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

theorem spine_eq_vertices_sup_edges (n : ℕ) : spine.{u} n = vertices n ⊔ edges n := by
  apply le_antisymm
  · intro q c hc
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h d =>
        have hsmall := (mem_spine_iff c).mp hc
        let l := SSet.stdSimplex.asOrderHom c 0
        let r := SSet.stdSimplex.asOrderHom c (Fin.last d)
        have hlr : l ≤ r := (SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le _)
        have hb (j : Fin (d + 1)) : l ≤ SSet.stdSimplex.asOrderHom c j ∧
            SSet.stdSimplex.asOrderHom c j ≤ r :=
          ⟨(SSet.stdSimplex.asOrderHom c).monotone (Fin.zero_le j),
            (SSet.stdSimplex.asOrderHom c).monotone (Fin.le_last j)⟩
        by_cases h : l = r
        · have hface : c ∈ (SSet.stdSimplex.face {l}).obj (op ⦋d⦌) := by
            rw [SSet.stdSimplex.mem_face_iff]
            intro j
            rw [Finset.mem_singleton]
            change SSet.stdSimplex.asOrderHom c j = l
            have hj := hb j
            exact le_antisymm (h.symm ▸ hj.2) hj.1
          exact (le_sup_of_le_left (le_iSup
            (fun i : Fin (n + 1) ↦ SSet.stdSimplex.face.{u} {i}) l)) _ hface
        · have hne : l.val ≠ r.val := fun he ↦ h (Fin.ext he)
          have hlrv : l.val ≤ r.val := hlr
          have hsmall' : r.val ≤ l.val + 1 := hsmall
          have hstep : r.val = l.val + 1 := by omega
          have hn : l.val < n := by have hr := r.isLt; omega
          let i : Fin n := ⟨l.val, hn⟩
          have hface : c ∈ (SSet.stdSimplex.face {i.castSucc, i.succ}).obj (op ⦋d⦌) := by
            rw [SSet.stdSimplex.mem_face_iff]
            intro j
            simp only [Finset.mem_insert, Finset.mem_singleton]
            have hj := hb j
            have hleft : l.val ≤ (SSet.stdSimplex.asOrderHom c j).val := hj.1
            have hright : (SSet.stdSimplex.asOrderHom c j).val ≤ r.val := hj.2
            by_cases he : (SSet.stdSimplex.asOrderHom c j).val = l.val
            · exact Or.inl (Fin.ext he)
            · apply Or.inr
              apply Fin.ext
              change (SSet.stdSimplex.asOrderHom c j).val = l.val + 1
              omega
          exact (le_sup_of_le_right (le_iSup
            (fun i : Fin n ↦ SSet.stdSimplex.face.{u} {i.castSucc, i.succ}) i)) _ hface
  · apply sup_le
    · exact iSup_le (fun i ↦ vertexFace_le i)
    · exact iSup_le (fun i ↦ edgeFace_le i)

end
end DaggerNativeStandardSpineGeometry
