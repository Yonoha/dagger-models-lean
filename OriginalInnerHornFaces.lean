import RigidificationCofProperLaws
import RigidificationCofExtremeBoundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornFaces

open BoundaryData PathFacets

variable {n : ℕ} (k : interior n)

/-- A face omits a vertex other than the missing horn index. -/
def Admissible (s : Finset (Fin (n + 2))) : Prop :=
  ∃ j, j ≠ k.val ∧ j ∉ s

theorem admissible_mono {s t : Finset (Fin (n + 2))}
    (ht : Admissible k t) (hst : s ⊆ t) : Admissible k s := by
  obtain ⟨j, hjk, hj⟩ := ht
  exact ⟨j, hjk, fun h ↦ hj (hst h)⟩

/-- The predicate is exactly membership of the original face ordinal in the horn. -/
theorem faceOrdinal_mem_iff (s : Finset (Fin (n + 2))) (hs : s.Nonempty) :
    SSet.stdSimplex.objEquiv.symm (faceOrdinal s hs) ∈
      (SSet.horn.{u} (n + 1) k.val).obj (op ⦋faceDimension s⦌) ↔
        Admissible k s := by
  classical
  change Set.range (SSet.stdSimplex.asOrderHom
    (SSet.stdSimplex.objEquiv.symm (faceOrdinal s hs))) ∪ {k.val} ≠ Set.univ ↔ _
  constructor
  · intro h
    by_contra ha
    apply h
    apply Set.eq_univ_iff_forall.mpr
    intro j
    by_cases hjk : j = k.val
    · exact Or.inr hjk
    · have hj : j ∈ s := by
        by_contra hj
        exact ha ⟨j, hjk, hj⟩
      left
      refine ⟨(faceOrderIso s hs).symm ⟨j, hj⟩, ?_⟩
      change ((faceOrderIso s hs) ((faceOrderIso s hs).symm ⟨j, hj⟩)).val = j
      simp only [OrderIso.apply_symm_apply]
  · rintro ⟨j, hjk, hj⟩ he
    have hmem : j ∈ Set.range (SSet.stdSimplex.asOrderHom
        (SSet.stdSimplex.objEquiv.symm (faceOrdinal s hs))) ∪ {k.val} := by
      rw [he]
      exact Set.mem_univ j
    rcases hmem with ⟨i, hi⟩ | hi
    · apply hj
      change (faceOrderIso s hs i).val = j at hi
      exact hi ▸ (faceOrderIso s hs i).property
    · exact hjk hi

/-- A proper interval omits an outer vertex, and every outer face belongs to an inner horn. -/
theorem interval_admissible (i j : Fin (n + 2))
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    Admissible k (Finset.Icc i j) := by
  by_cases hi : i = 0
  · refine ⟨Fin.last (n + 1), ne_of_gt k.property.2, ?_⟩
    intro h
    have hj : j = Fin.last (n + 1) :=
      le_antisymm (Fin.le_last j) (Finset.mem_Icc.mp h).2
    exact hp ⟨hi, hj⟩
  · refine ⟨0, ne_of_lt k.property.1, ?_⟩
    intro h
    exact hi (le_antisymm (Finset.mem_Icc.mp h).1 (Fin.zero_le i))

/-- Only the permitted codimension-one faces are admitted. -/
theorem complement_singleton_admissible_iff (j : Fin (n + 2)) :
    Admissible k ({j}ᶜ : Finset (Fin (n + 2))) ↔ j ≠ k.val := by
  classical
  simp only [Admissible, Finset.mem_compl, Finset.mem_singleton, not_not]
  constructor
  · rintro ⟨l, hlk, rfl⟩
    exact hlk
  · intro hjk
    exact ⟨j, hjk, rfl⟩

/-- Every vertex is available; no boundary extension is selected. -/
theorem singleton_admissible (i : Fin (n + 2)) :
    Admissible k ({i} : Finset (Fin (n + 2))) := by
  apply admissible_mono k (interval_admissible k i i (diagonal_proper i))
  intro j hj
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  exact Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩

end DaggerOrdinaryRigidificationCof.InnerHornFaces
