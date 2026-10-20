import TopCatModelCategory.SSet.Horn

/-! The actual missing face completes a native horn to the original simplex boundary. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerNativeHornMissingFaceGeometry
noncomputable section

theorem horn_sup_missing_face (n : ℕ) (i : Fin (n + 1)) :
    SSet.horn.{u} n i ⊔ SSet.stdSimplex.face {i}ᶜ = SSet.boundary n := by
  apply le_antisymm
  · exact sup_le (SSet.horn_le_boundary i) (SSet.face_le_boundary i)
  · rw [SSet.boundary_eq_iSup]
    apply iSup_le
    intro j
    by_cases h : j = i
    · subst j
      exact le_sup_right
    · exact le_sup_of_le_left (SSet.face_le_horn j i h)

theorem range_succAbove_union_singleton {n : ℕ} {A : Type*}
    (i : Fin (n + 2)) (f : A → Fin (n + 1)) :
    Set.range (fun a ↦ i.succAbove (f a)) ∪ {i} = Set.univ ↔ Function.Surjective f := by
  constructor
  · intro h j
    have hj : i.succAbove j ∈ Set.range (fun a ↦ i.succAbove (f a)) ∪ {i} := by
      rw [h]
      trivial
    rcases hj with ⟨a, ha⟩ | ha
    · exact ⟨a, Fin.succAbove_right_injective ha⟩
    · exact False.elim ((Fin.succAbove_ne i j) ha)
  · intro h
    apply Set.eq_univ_of_forall
    intro j
    by_cases hj : j = i
    · exact Or.inr hj
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
      obtain ⟨a, rfl⟩ := h k
      exact Or.inl ⟨a, hk⟩

theorem missing_face_preimage_horn (n : ℕ) (i : Fin (n + 2)) :
    (SSet.horn.{u} (n + 1) i).preimage (SSet.stdSimplex.δ i) = SSet.boundary n := by
  ext k x
  change (Set.range (fun a ↦ i.succAbove (SSet.stdSimplex.asOrderHom x a)) ∪ {i} ≠
    Set.univ) ↔ ¬ Function.Surjective (SSet.stdSimplex.asOrderHom x)
  exact not_congr (range_succAbove_union_singleton i _)

end
end DaggerNativeHornMissingFaceGeometry
