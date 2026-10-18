import ChosenNecklaceVertices

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode.Bead

variable {T : NecklaceCode} (b c : T.Bead)

theorem ext_endpoints (hl : b.left = c.left) (hr : b.right = c.right) : b = c := by
  cases b
  cases c
  cases hl
  cases hr
  rfl

theorem left_injective (h : b.left = c.left) : b = c := by
  apply b.ext_endpoints c h
  apply le_antisymm
  · by_contra hn
    have hcr : c.right < b.right := lt_of_not_ge hn
    exact b.no_joint c.right c.right_mem (h ▸ c.lt) hcr
  · by_contra hn
    have hbr : b.right < c.right := lt_of_not_ge hn
    exact c.no_joint b.right b.right_mem (h.symm ▸ b.lt) hbr

theorem right_le_left (h : b.left < c.left) : b.right ≤ c.left := by
  by_contra hn
  exact b.no_joint c.left c.left_mem h (lt_of_not_ge hn)

/-- Distinct beads meet only at one of their actual common endpoints. -/
theorem mem_inter_iff (hne : b ≠ c) (v : Fin (T.len + 1)) :
    v ∈ b.interval ∩ c.interval ↔
      (b.right = c.left ∧ v = b.right) ∨ (c.right = b.left ∧ v = c.right) := by
  constructor
  · intro hv
    obtain ⟨hb, hc⟩ := Finset.mem_inter.mp hv
    obtain ⟨hbl, hbr⟩ := Finset.mem_Icc.mp hb
    obtain ⟨hcl, hcr⟩ := Finset.mem_Icc.mp hc
    rcases lt_trichotomy b.left c.left with h | h | h
    · have hd := b.right_le_left c h
      have he := le_antisymm hd (hcl.trans hbr)
      left
      exact ⟨he, le_antisymm hbr (he ▸ hcl)⟩
    · exact False.elim (hne (b.left_injective c h))
    · have hd := c.right_le_left b h
      have he := le_antisymm hd (hbl.trans hcr)
      right
      exact ⟨he, le_antisymm hcr (he ▸ hbl)⟩
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
    · exact Finset.mem_inter.mpr ⟨b.right_mem_interval, h.symm ▸ c.left_mem_interval⟩
    · exact Finset.mem_inter.mpr ⟨h.symm ▸ b.left_mem_interval, c.right_mem_interval⟩

theorem interval_inter_of_adjacent (h : b.right = c.left) :
    b.interval ∩ c.interval = {b.right} := by
  ext v
  simp only [interval, Finset.mem_inter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hbr⟩, ⟨hcl, _⟩⟩
    exact le_antisymm hbr (h ▸ hcl)
  · rintro rfl
    exact ⟨⟨b.lt.le, le_rfl⟩, ⟨h ▸ le_rfl, h.symm ▸ c.lt.le⟩⟩

theorem interval_inter_of_separated (h : b.right < c.left) :
    b.interval ∩ c.interval = ∅ := by
  ext v
  simp only [interval, Finset.mem_inter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
  rintro ⟨⟨_, hbr⟩, ⟨hcl, _⟩⟩
  exact (not_lt_of_ge (hcl.trans hbr)) h

theorem face_inter_of_adjacent (h : b.right = c.left) :
    face.{u} b ⊓ c.face = SSet.stdSimplex.face {b.right} := by
  rw [face, face, SSet.stdSimplex.face_inter_face]
  exact congrArg SSet.stdSimplex.face (b.interval_inter_of_adjacent c h)

theorem face_inter_of_separated (h : b.right < c.left) :
    face.{u} b ⊓ c.face = SSet.stdSimplex.face ∅ := by
  rw [face, face, SSet.stdSimplex.face_inter_face]
  exact congrArg SSet.stdSimplex.face (b.interval_inter_of_separated c h)

end DaggerChosenRigidificationNecklace.NecklaceCode.Bead
