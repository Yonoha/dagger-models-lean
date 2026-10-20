import BisimplicialPrescribedCollapse
import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
SOURCE-ONLY FINITE PROOF DRAFT. No Lean call has checked any body in this file.
The imported positions/rho source is unchanged and itself remains an uncompiled candidate.
All exported finite conclusions below are unconditional in the original n/I.
-/

open CategoryTheory Simplicial

namespace DaggerBisimplicialDiagonal

theorem positions_mem_iff {n : ℕ} (I : Finset (Fin n)) (v : ℕ) :
    v ∈ positions I ↔ ∃ i ∈ I, i.val = v := by
  simp only [positions, Finset.mem_sort, Finset.mem_image]

theorem positions_mem {n : ℕ} (I : Finset (Fin n)) (i : Fin n) :
    i.val ∈ positions I ↔ i ∈ I := by
  rw [positions_mem_iff]
  constructor
  · rintro ⟨j, hj, hji⟩
    have h : j = i := Fin.ext hji
    simpa only [h] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem positions_sorted {n : ℕ} (I : Finset (Fin n)) : (positions I).SortedLT :=
  Finset.sortedLT_sort (I.image Fin.val)

/-- Finite order bound only; this does not construct any epimorphism or alter rho. -/
private theorem finite_upper_bound (c : ℕ) :
    ∀ (n : ℕ) (f : Fin c → ℕ), StrictMono f → (∀ i, f i < n) → c ≤ n →
      ∀ i, f i ≤ n - c + i.val := by
  induction c with
  | zero =>
    intro n f hf hb hc i
    exact Fin.elim0 i
  | succ c ih =>
    intro n f hf hb hc i
    cases i using Fin.lastCases with
    | last =>
      have hlast := hb (Fin.last c)
      change f (Fin.last c) ≤ n - (c + 1) + c
      omega
    | cast j =>
      have hb' : ∀ i : Fin c, f i.castSucc < n - 1 := by
        intro i
        have hlt := hf (Fin.castSucc_lt_last i)
        have hlast := hb (Fin.last c)
        omega
      have hc' : c ≤ n - 1 := by omega
      have h := ih (n - 1) (fun i => f i.castSucc)
        (hf.comp Fin.strictMono_castSucc) hb' hc' j
      change f j.castSucc ≤ n - (c + 1) + j.val
      omega

theorem positions_get_le {n : ℕ} (I : Finset (Fin n)) (k : ℕ)
    (hk : k < (positions I).length) :
    (positions I)[k] ≤ n - I.card + k := by
  have hb : ∀ j : Fin (positions I).length, (positions I).get j < n := by
    intro j
    rcases (positions_mem_iff I ((positions I).get j)).1 (List.get_mem _ j) with
      ⟨i, _hi, heq⟩
    rw [← heq]
    exact i.isLt
  have hc : (positions I).length ≤ n := by
    rw [positions_length]
    simpa only [Fintype.card_fin] using I.card_le_univ
  have h := finite_upper_bound (positions I).length n (positions I).get
    (positions_sorted I).strictMono_get hb hc ⟨k, hk⟩
  simpa only [List.get_eq_getElem, positions_length] using h

theorem positions_admissible {n : ℕ} (I : Finset (Fin n)) :
    SimplexCategoryGenRel.IsAdmissible (n - I.card) (positions I) := by
  apply SimplexCategoryGenRel.isAdmissible_iff_pairwise_and_le.mpr
  exact ⟨(positions_sorted I).pairwise, fun k hk => positions_get_le I k hk⟩

/-- P_sigma needs only the original list and dimensional equality, not admissibility. -/
theorem standardσ_P_σ (L : List ℕ) {m₁ m₂ : ℕ} (h : m₂ + L.length = m₁) :
    SimplexCategoryGenRel.P_σ (SimplexCategoryGenRel.standardσ L h) := by
  induction L generalizing m₁ m₂ with
  | nil =>
    have hm : m₂ = m₁ := by simpa only [List.length_nil, Nat.add_zero] using h
    subst m₁
    simpa only [SimplexCategoryGenRel.standardσ_nil] using
      MorphismProperty.id_mem SimplexCategoryGenRel.P_σ (SimplexCategoryGenRel.mk m₂)
  | cons a L ih =>
    rw [SimplexCategoryGenRel.standardσ_cons]
    exact MorphismProperty.comp_mem SimplexCategoryGenRel.P_σ _ _
      (ih (by simp only [List.length_cons] at h; omega))
      (SimplexCategoryGenRel.P_σ.σ (Fin.ofNat _ a))

theorem rho_isSplitEpi {n : ℕ} (I : Finset (Fin n)) : IsSplitEpi (rho I) := by
  exact SimplexCategoryGenRel.isSplitEpi_toSimplexCategory_map_of_P_σ
    (standardσ_P_σ (positions I) (positions_dimension I))

theorem rho_eval {n : ℕ} (I : Finset (Fin n)) (j : ℕ) (hj : j < n + 1) :
    ((rho I).toOrderHom ⟨j, hj⟩ : ℕ) =
      SimplexCategoryGenRel.simplicialEvalσ (positions I) j :=
  rho_eval_of_admissible I (positions_admissible I) j hj

theorem rho_adjacent_iff {n : ℕ} (I : Finset (Fin n)) (i : Fin n) :
    (rho I).toOrderHom i.castSucc = (rho I).toOrderHom i.succ ↔ i ∈ I := by
  have hi : i.val < n := i.isLt
  have h0 : i.val < n + 1 := by omega
  have h1 : i.val + 1 < n + 1 := by omega
  rw [Fin.ext_iff]
  change ((rho I).toOrderHom ⟨i.val, h0⟩ : ℕ) =
    ((rho I).toOrderHom ⟨i.val + 1, h1⟩ : ℕ) ↔ i ∈ I
  rw [rho_eval I i.val h0, rho_eval I (i.val + 1) h1]
  have hmem := SimplexCategoryGenRel.mem_isAdmissible_iff
    (positions I) (positions_admissible I) i.val
  constructor
  · intro heq
    apply (positions_mem I i).1
    apply hmem.2
    refine ⟨?_, heq⟩
    rw [positions_dimension]
    exact hi
  · intro h
    exact (hmem.1 ((positions_mem I i).2 h)).2

theorem rho_empty (n : ℕ) : rho (∅ : Finset (Fin n)) = 𝟙 ⦋n⦌ := by
  simp [rho, positions]
  exact SimplexCategoryGenRel.toSimplexCategory.map_id _

theorem rho_univ_value (n : ℕ) (t : Fin (n + 1)) :
    (rho (Finset.univ : Finset (Fin n))).toOrderHom t = 0 := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  apply Fin.ext
  change ((rho (Finset.univ : Finset (Fin n))).toOrderHom t).val = 0
  have ht := ((rho (Finset.univ : Finset (Fin n))).toOrderHom t).isLt
  change ((rho (Finset.univ : Finset (Fin n))).toOrderHom t).val <
    n - (Finset.univ : Finset (Fin n)).card + 1 at ht
  have hdim : n - (Finset.univ : Finset (Fin n)).card = 0 := by
    rw [hcard, Nat.sub_self]
  omega

theorem rho_first {n : ℕ} (I : Finset (Fin n)) :
    (rho I).toOrderHom (0 : Fin (n + 1)) = 0 := by
  apply Fin.ext
  change ((rho I).toOrderHom ⟨0, Nat.zero_lt_succ n⟩ : ℕ) = 0
  rw [rho_eval I 0 (Nat.zero_lt_succ n)]
  exact SimplexCategoryGenRel.simplicialEvalσ_of_le_mem
    (positions I) 0 (fun k _hk => Nat.zero_le k)

theorem rho_last {n : ℕ} (I : Finset (Fin n)) :
    (rho I).toOrderHom (Fin.last n) = Fin.last (n - I.card) := by
  letI := rho_isSplitEpi I
  have hs : Function.Surjective (rho I).toOrderHom :=
    SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi (rho I))
  rcases hs (Fin.last (n - I.card)) with ⟨t, ht⟩
  apply le_antisymm
  · exact Fin.le_last _
  · rw [← ht]
    exact (rho I).toOrderHom.monotone (Fin.le_last t)

end DaggerBisimplicialDiagonal
