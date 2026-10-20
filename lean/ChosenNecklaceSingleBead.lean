import ChosenNecklaceIntersections
import ChosenNecklaceVertices

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

def single (n : ℕ) : NecklaceCode where
  len := n
  joints := {0, Fin.last n}
  first_mem := by simp
  last_mem := by simp

theorem mem_single_joints (n : ℕ) (v : Fin (n + 1)) :
    v ∈ (single n).joints ↔ v = 0 ∨ v = Fin.last n := by
  simp [single]

def singleBead (n : ℕ) (hn : 0 < n) : Bead (single n) where
  left := 0
  right := Fin.last n
  left_mem := by simp [single]
  right_mem := by simp [single]
  lt := by change 0 < n; exact hn
  no_joint v hv hl hr := by
    rcases (mem_single_joints n v).mp hv with h | h
    · subst v; exact (lt_irrefl _ hl).elim
    · subst v; exact (lt_irrefl _ hr).elim

theorem singleBead_interval (n : ℕ) (hn : 0 < n) :
    (singleBead n hn).interval = Finset.univ := by
  ext v
  simp only [Bead.interval, singleBead, Finset.mem_Icc, Finset.mem_univ, iff_true]
  exact ⟨Fin.zero_le v, Fin.le_last v⟩

theorem single_complex_top (n : ℕ) : complex.{u} (single n) = ⊤ := by
  by_cases hn : n = 0
  · subst n
    exact complex_eq_top_of_zero (single 0) rfl
  · apply top_unique
    intro q x _
    obtain ⟨q⟩ := q
    induction q using SimplexCategory.rec with | _ k
    apply (mem_complex_iff (single n) x).mpr
    right
    refine ⟨singleBead n (Nat.pos_of_ne_zero hn), ?_⟩
    intro i
    rw [singleBead_interval]
    exact Finset.mem_univ _

def singleIso (n : ℕ) : toSSet.{u} (single n) ≅ Δ[n] :=
  complexIso (single n) ≪≫ SSet.Subcomplex.eqToIso (single_complex_top n) ≪≫
    SSet.Subcomplex.topIso _

theorem singleIso_hom (n : ℕ) : (singleIso.{u} n).hom = inclusion (single n) := by
  unfold singleIso inclusion
  simp only [Iso.trans_hom]
  congr 1

theorem singleIso_vertex (n : ℕ) (x : (toSSet.{u} (single n)).obj (op ⦋0⦌)) :
    SSet.stdSimplex.obj₀Equiv ((singleIso n).hom.app _ x) =
      ((single n).verticesEquiv x).down := by
  rw [singleIso_hom]
  exact (verticesEquiv_down (single n) x).symm

end

end DaggerChosenRigidificationNecklace.NecklaceCode
