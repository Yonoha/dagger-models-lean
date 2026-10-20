import DaggerModels.FreeDaggerCell
import DaggerModels.RelativeCellMaps
import DaggerModels.RelativeCellOrbits

/-!
# Separation of interiors of the chosen relative dagger cells

This is the interior-injectivity step of the relative boundary-cell construction
in Part I, `dj.lem.free-cof`. Eilenberg–Zilber uniqueness and the separation of
the chosen dagger-orbit representatives suffice. The characteristic maps need
not be monomorphisms. Zero-cells have a single copy, while positive cells have
two copies and no self-conjugate chosen simplex.
-/

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace DaggerModels.RelativeCellSeparation

open DaggerSSet FreeDaggerCell RelativeCellMaps

variable {X Y : DaggerSSet.{u}} {i : X ⟶ Y}

private theorem epi_rev {n k : ℕ} (α : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] :
    Epi (SimplexCategory.rev.map α) := by
  change Epi (SimplexCategory.revEquivalence.functor.map α)
  infer_instance

private theorem epi_to_zero {k : ℕ} (α : ⦋k⦌ ⟶ ⦋0⦌) : Epi α := by
  apply SimplexCategory.epi_iff_surjective.2
  exact fun j ↦ ⟨0, Subsingleton.elim (α := Fin 1) _ _⟩

/-- Equality of left-copy ambient values identifies both the cell and its epimorphic label. -/
theorem left_values_separate {n k : ℕ} (c : CellReps i n) (r s : c.R)
    (α β : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] [Epi β]
    (h : Y.toSSet.map α.op (c.rep r).1.1 = Y.toSSet.map β.op (c.rep s).1.1) :
    r = s ∧ α = β := by
  obtain ⟨hσ, hα⟩ := RelativeCellBoundary.relative_stage_normal_form_unique
    (Y.toSSet.map α.op (c.rep r).1.1) (c.rep r).1 (c.rep s).1 α β rfl h
  exact ⟨c.separated r s (Or.inl (Subtype.ext hσ)), hα⟩

/-- Equality of right-copy values retains the reversed labels in the uniqueness argument. -/
theorem right_values_separate {n k : ℕ} (c : CellReps i n) (r s : c.R)
    (α β : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] [Epi β]
    (h : Y.toSSet.map (SimplexCategory.rev.map α).op (Y.daggerSimplex (c.rep r).1.1) =
      Y.toSSet.map (SimplexCategory.rev.map β).op (Y.daggerSimplex (c.rep s).1.1)) :
    r = s ∧ α = β := by
  let : Epi (SimplexCategory.rev.map α) := epi_rev α
  let : Epi (SimplexCategory.rev.map β) := epi_rev β
  obtain ⟨hσ, hα⟩ := RelativeCellBoundary.relative_stage_normal_form_unique
    (Y.toSSet.map (SimplexCategory.rev.map α).op (Y.daggerSimplex (c.rep r).1.1))
    (newNonDegenerateDagger i n (c.rep r)).1
    (newNonDegenerateDagger i n (c.rep s)).1
    (SimplexCategory.rev.map α) (SimplexCategory.rev.map β) rfl h
  have hreps := (newNonDegenerateDagger i n).injective (Subtype.ext hσ)
  refine ⟨c.separated r s (Or.inl hreps), ?_⟩
  simpa only [SimplexCategory.rev_map_rev_map] using congrArg SimplexCategory.rev.map hα

/-- A positive cell's left value never equals a chosen cell's right value. -/
theorem left_values_ne_right {n k : ℕ} (c : CellReps i n) (hn : 0 < n) (r s : c.R)
    (α β : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] [Epi β] :
    Y.toSSet.map α.op (c.rep r).1.1 ≠
      Y.toSSet.map (SimplexCategory.rev.map β).op (Y.daggerSimplex (c.rep s).1.1) := by
  intro h
  let : Epi (SimplexCategory.rev.map β) := epi_rev β
  have hσ := (RelativeCellBoundary.relative_stage_normal_form_unique
    (Y.toSSet.map α.op (c.rep r).1.1) (c.rep r).1
    (newNonDegenerateDagger i n (c.rep s)).1 α (SimplexCategory.rev.map β) rfl h).1
  exact c.rep_ne_dagger_rep hn r s (Subtype.ext hσ)

variable [Mono i]

theorem cellMap_left_val {n k : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (α : ⦋k⦌ ⟶ ⦋n⦌) :
    ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
      (op ⦋k⦌) (left α)).1 = Y.toSSet.map α.op σ.1 :=
  cellMap_inl_app_val i σ α

theorem cellMap_right_val {n k : ℕ} (σ : Y.toSSet.nonDegenerate n)
    (α : ⦋k⦌ ⟶ ⦋n⦌) :
    ((cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction σ).hom.app
      (op ⦋k⦌) (right α)).1 =
        Y.toSSet.map (SimplexCategory.rev.map α).op (Y.daggerSimplex σ.1) :=
  cellMap_inr_app_val i σ α

/-- Equality of interior characteristic values identifies both the chosen cell and
the simplex within that actual free cell. No characteristic map is assumed mono. -/
theorem cellMap_separates {n k : ℕ} (c : CellReps i n) (r s : c.R)
    (x y : (FreeDaggerPushout.underlying (Δ[n] : SSet.{u})) _⦋k⦌)
    (hx : x ∉ boundaryRange n k) (hy : y ∉ boundaryRange n k)
    (h : (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction
        (c.rep r).1).hom.app (op ⦋k⦌) x =
      (cellMap i FreeDaggerPushout.functor FreeDaggerPushout.adjunction
        (c.rep s).1).hom.app (op ⦋k⦌) y) :
    r = s ∧ x = y := by
  by_cases hn : 0 < n
  · obtain ⟨side, α, hα, rfl⟩ := exists_copy_epi x hx
    obtain ⟨side', β, hβ, rfl⟩ := exists_copy_epi y hy
    let : Epi α := hα
    let : Epi β := hβ
    have hval := congrArg Subtype.val h
    cases side <;> cases side'
    · simp only [copy_false, cellMap_left_val] at hval
      obtain ⟨hrs, hαβ⟩ := left_values_separate c r s α β hval
      exact ⟨hrs, congrArg (copy false) hαβ⟩
    · simp only [copy_false, copy_true, cellMap_left_val, cellMap_right_val] at hval
      exact False.elim (left_values_ne_right c hn r s α β hval)
    · simp only [copy_false, copy_true, cellMap_left_val, cellMap_right_val] at hval
      exact False.elim (left_values_ne_right c hn s r β α hval.symm)
    · simp only [copy_true, cellMap_right_val] at hval
      obtain ⟨hrs, hαβ⟩ := right_values_separate c r s α β hval
      exact ⟨hrs, congrArg (copy true) hαβ⟩
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    obtain ⟨α, rfl, _⟩ := existsUnique_left_zero x
    obtain ⟨β, rfl, _⟩ := existsUnique_left_zero y
    let : Epi α := epi_to_zero α
    let : Epi β := epi_to_zero β
    have hval := congrArg Subtype.val h
    simp only [cellMap_left_val] at hval
    obtain ⟨hrs, hαβ⟩ := left_values_separate c r s α β hval
    exact ⟨hrs, congrArg left hαβ⟩

end DaggerModels.RelativeCellSeparation
