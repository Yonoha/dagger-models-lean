import OriginalAntiInvolutiveNormalMonoTransfinite
import DaggerModels.FreeInvolution

/-!
# Free orbits of the actual new anti-involutive simplices

For an arbitrary anti-involutive map, reversal preserves the new
nondegenerate simplices in every degree. The original all-degree `NormalMono`
predicate is equivalent to these complements splitting into free two-element
orbits, including degree zero. This supplies the orbit indices and chosen
cells needed for a relative free-boundary attachment construction; it does
not assert that the attachment squares have yet been constructed.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveNormalGenerators

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.FreeInvolution

/-- The nondegenerate simplices omitted by the original anti-involutive map. -/
def NewNonDegenerate {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) (n : ℕ) : Type u :=
  {σ : Y.toSSet.nonDegenerate n // σ.1 ∉ Set.range (f.hom.app (op ⦋n⦌))}

@[ext] theorem NewNonDegenerate.ext {X Y : AntiInvolutiveSSet.{u}} {f : X ⟶ Y}
    {n : ℕ} {σ τ : NewNonDegenerate f n} (h : σ.1.1 = τ.1.1) : σ = τ :=
  Subtype.ext (Subtype.ext h)

/-- Reversal preserves the old image, so it preserves its complement. -/
theorem dagger_not_mem_range {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y)
    {n : ℕ} {x : Y.toSSet _⦋n⦌}
    (hx : x ∉ Set.range (f.hom.app (op ⦋n⦌))) :
    Y.daggerSimplex x ∉ Set.range (f.hom.app (op ⦋n⦌)) := by
  rintro ⟨a, ha⟩
  apply hx
  refine ⟨X.daggerSimplex a, ?_⟩
  exact (f.dagger_comm a).trans ((congrArg Y.daggerSimplex ha).trans (Y.dagger_dagger x))

/-- Reversal preserves degeneracy for the original anti-involutive object. -/
theorem dagger_mem_degenerate (Y : AntiInvolutiveSSet.{u}) {n : ℕ}
    {x : Y.toSSet _⦋n⦌} (hx : x ∈ Y.toSSet.degenerate n) :
    Y.daggerSimplex x ∈ Y.toSSet.degenerate n := by
  obtain ⟨m, hm, g, y, rfl⟩ := hx
  exact ⟨m, hm, SimplexCategory.rev.map g, Y.daggerSimplex y,
    (Y.dagger_map g y).symm⟩

theorem dagger_mem_nonDegenerate_iff (Y : AntiInvolutiveSSet.{u}) {n : ℕ}
    (x : Y.toSSet _⦋n⦌) :
    Y.daggerSimplex x ∈ Y.toSSet.nonDegenerate n ↔
      x ∈ Y.toSSet.nonDegenerate n := by
  constructor
  · intro h hx
    exact h (dagger_mem_degenerate Y hx)
  · intro h hx
    have hh := dagger_mem_degenerate Y hx
    rw [Y.dagger_dagger] at hh
    exact h hh

/-- Reversal acts on the actual complement of nondegenerate simplices. -/
def newDagger {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    NewNonDegenerate f n ≃ NewNonDegenerate f n where
  toFun σ := ⟨⟨Y.daggerSimplex σ.1.1,
    (dagger_mem_nonDegenerate_iff Y σ.1.1).2 σ.1.2⟩,
    dagger_not_mem_range f σ.2⟩
  invFun σ := ⟨⟨Y.daggerSimplex σ.1.1,
    (dagger_mem_nonDegenerate_iff Y σ.1.1).2 σ.1.2⟩,
    dagger_not_mem_range f σ.2⟩
  left_inv σ := NewNonDegenerate.ext (Y.dagger_dagger σ.1.1)
  right_inv σ := NewNonDegenerate.ext (Y.dagger_dagger σ.1.1)

@[simp] theorem newDagger_val {X Y : AntiInvolutiveSSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (σ : NewNonDegenerate f n) :
    (newDagger f n σ).1.1 = Y.daggerSimplex σ.1.1 := rfl

theorem newDagger_involutive {X Y : AntiInvolutiveSSet.{u}}
    (f : X ⟶ Y) (n : ℕ) : Function.Involutive (newDagger f n) :=
  (newDagger f n).left_inv

/-- The unchanged DCH-style normality condition makes every new orbit free. -/
theorem newDagger_ne {X Y : AntiInvolutiveSSet.{u}} {f : X ⟶ Y}
    (hf : NormalMono f) (n : ℕ) (σ : NewNonDegenerate f n) :
    newDagger f n σ ≠ σ := by
  intro h
  exact hf.2 n σ.1.1 σ.1.2 σ.2 (congrArg (fun τ ↦ τ.1.1) h)

/-- Actual reversal orbits of the new nondegenerate simplices. -/
def NewCellOrbit {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) (n : ℕ) : Type u :=
  FreeInvolution.Orbit (newDagger f n) (newDagger_involutive f n)

/-- For a normal map, each orbit has exactly two distinct new simplices. -/
noncomputable def newCellSplit {X Y : AntiInvolutiveSSet.{u}} {f : X ⟶ Y}
    (hf : NormalMono f) (n : ℕ) :
    NewNonDegenerate f n ≃ NewCellOrbit f n × Bool :=
  FreeInvolution.equiv _ _ (newDagger_ne hf n)

theorem newCellSplit_dagger {X Y : AntiInvolutiveSSet.{u}} {f : X ⟶ Y}
    (hf : NormalMono f) (n : ℕ) (σ : NewNonDegenerate f n) :
    newCellSplit hf n (newDagger f n σ) =
      ((newCellSplit hf n σ).1, !(newCellSplit hf n σ).2) :=
  FreeInvolution.equiv_involution _ _ _ σ

/-- Normality is recognized by genuine free two-element-orbit splittings
of the actual relative nondegenerate simplices in every degree. -/
theorem normalMono_iff_free_new_cells {X Y : AntiInvolutiveSSet.{u}}
    (f : X ⟶ Y) : NormalMono f ↔
      Mono f.hom ∧ ∀ n : ℕ, ∃ (R : Type u)
        (e : NewNonDegenerate f n ≃ R × Bool),
        ∀ σ, e (newDagger f n σ) = ((e σ).1, !(e σ).2) := by
  constructor
  · intro hf
    exact ⟨hf.1, fun n ↦ ⟨NewCellOrbit f n, newCellSplit hf n,
      newCellSplit_dagger hf n⟩⟩
  · rintro ⟨hm, hs⟩
    refine ⟨hm, ?_⟩
    intro n x hx hnew hfix
    let σ : NewNonDegenerate f n := ⟨⟨x, hx⟩, hnew⟩
    obtain ⟨R, e, he⟩ := hs n
    have hσ : newDagger f n σ = σ := NewNonDegenerate.ext hfix
    have hb := congrArg Prod.snd (he σ)
    rw [hσ] at hb
    cases hbit : (e σ).2 <;> simp [hbit] at hb

end DaggerModels.OriginalAntiInvolutiveNormalGenerators
