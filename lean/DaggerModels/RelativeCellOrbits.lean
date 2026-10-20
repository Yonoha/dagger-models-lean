import DaggerModels.FreeCofibration
import DaggerModels.FreeInvolution

/-!
# Representatives of the new relative dagger cells

The new nondegenerate simplices are defined using the original map's actual
image. Dagger restricts to an involution on this type. A free cofibration
makes it free in positive dimensions, so its orbit quotient supplies the
chosen representatives in Part I, `dj.lem.free-cof`. In dimension zero we
instead index the individual new vertices; no Bool splitting is asserted.
-/

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.DaggerSSet

/-- The actual new nondegenerate simplices of the original dagger-compatible map. -/
def NewNonDegenerate {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ) : Type u :=
  {σ : Y.toSSet.nonDegenerate n // σ.1 ∉ Set.range (i.hom.app (op ⦋n⦌))}

@[ext] theorem NewNonDegenerate.ext {X Y : DaggerSSet.{u}} {i : X ⟶ Y} {n : ℕ}
    {σ τ : NewNonDegenerate i n} (h : σ.1.1 = τ.1.1) : σ = τ :=
  Subtype.ext (Subtype.ext h)

/-- Dagger preserves the complement of the image, even without a monicity assumption. -/
theorem dagger_not_mem_range {X Y : DaggerSSet.{u}} (i : X ⟶ Y) {n : ℕ}
    {x : Y.toSSet _⦋n⦌} (hx : x ∉ Set.range (i.hom.app (op ⦋n⦌))) :
    Y.daggerSimplex x ∉ Set.range (i.hom.app (op ⦋n⦌)) := by
  rintro ⟨a, ha⟩
  apply hx
  refine ⟨X.daggerSimplex a, ?_⟩
  exact (i.dagger_comm a).trans ((congrArg Y.daggerSimplex ha).trans (Y.dagger_dagger x))

/-- The original dagger restricts to the new nondegenerate simplices. -/
def newNonDegenerateDagger {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ) :
    NewNonDegenerate i n ≃ NewNonDegenerate i n where
  toFun σ := ⟨Y.nonDegenerateEquiv n σ.1, dagger_not_mem_range i σ.2⟩
  invFun σ := ⟨Y.nonDegenerateEquiv n σ.1, dagger_not_mem_range i σ.2⟩
  left_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    exact Y.dagger_dagger σ.1.1
  right_inv σ := by
    apply Subtype.ext
    apply Subtype.ext
    exact Y.dagger_dagger σ.1.1

@[simp] theorem newNonDegenerateDagger_val {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ)
    (σ : NewNonDegenerate i n) :
    (newNonDegenerateDagger i n σ).1.1 = Y.daggerSimplex σ.1.1 := rfl

theorem newNonDegenerateDagger_involutive {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ) :
    Function.Involutive (newNonDegenerateDagger i n) :=
  (newNonDegenerateDagger i n).left_inv

/-- Freeness is obtained directly from the unchanged free-cofibration predicate. -/
theorem newNonDegenerateDagger_ne {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) {n : ℕ} (hn : 0 < n) (σ : NewNonDegenerate i n) :
    newNonDegenerateDagger i n σ ≠ σ := by
  intro h
  exact hi.2 n hn σ.1.1 σ.1.2 σ.2 (congrArg (fun τ ↦ τ.1.1) h)

/-- Every individual new vertex is fixed, as required by the original dagger definition. -/
@[simp] theorem newNonDegenerateDagger_zero {X Y : DaggerSSet.{u}} (i : X ⟶ Y)
    (σ : NewNonDegenerate i 0) : newNonDegenerateDagger i 0 σ = σ := by
  apply Subtype.ext
  apply Subtype.ext
  exact Y.dagger_vertex σ.1.1

/-- New nondegenerate zero-simplices are exactly the individual new vertices. -/
def newNonDegenerateZeroEquiv {X Y : DaggerSSet.{u}} (i : X ⟶ Y) :
    NewNonDegenerate i 0 ≃
      {v : Y.toSSet _⦋0⦌ // v ∉ Set.range (i.hom.app (op ⦋0⦌))} where
  toFun σ := ⟨σ.1.1, σ.2⟩
  invFun v := ⟨⟨v.1, by simp⟩, v.2⟩
  left_inv σ := rfl
  right_inv v := rfl

/-- The actual dagger orbits of new nondegenerate simplices. -/
def NewCellOrbit {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ) : Type u :=
  FreeInvolution.Orbit (newNonDegenerateDagger i n) (newNonDegenerateDagger_involutive i n)

/-- A chosen new simplex in each actual dagger orbit. -/
noncomputable def newCellRepresentative {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ) :
    NewCellOrbit i n → NewNonDegenerate i n :=
  FreeInvolution.representative (newNonDegenerateDagger i n)
    (newNonDegenerateDagger_involutive i n)

theorem newCellRepresentative_cover {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ)
    (σ : NewNonDegenerate i n) : ∃ r : NewCellOrbit i n,
      σ = newCellRepresentative i n r ∨
        σ = newNonDegenerateDagger i n (newCellRepresentative i n r) :=
  ⟨FreeInvolution.orbit _ _ σ, FreeInvolution.representative_cover _ _ σ⟩

theorem newCellRepresentative_separated {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ)
    {r s : NewCellOrbit i n} (h : newCellRepresentative i n r = newCellRepresentative i n s ∨
      newCellRepresentative i n r = newNonDegenerateDagger i n (newCellRepresentative i n s)) :
    r = s := FreeInvolution.representative_separated _ _ h

/-- Positive-dimensional new simplices split into the two elements of each free orbit. -/
noncomputable def newCellSplit {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) (hn : 0 < n) :
    NewNonDegenerate i n ≃ NewCellOrbit i n × Bool :=
  FreeInvolution.equiv _ _ (newNonDegenerateDagger_ne hi hn)

/-- The positive-dimensional split identifies dagger with the Bool flip. -/
theorem newCellSplit_dagger {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) (hn : 0 < n) (σ : NewNonDegenerate i n) :
    newCellSplit hi n hn (newNonDegenerateDagger i n σ) =
      ((newCellSplit hi n hn σ).1, !(newCellSplit hi n hn σ).2) :=
  FreeInvolution.equiv_involution _ _ _ σ

@[simp] theorem newCellSplit_symm_false {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) (hn : 0 < n) (r : NewCellOrbit i n) :
    (newCellSplit hi n hn).symm (r, false) = newCellRepresentative i n r := rfl

@[simp] theorem newCellSplit_symm_true {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) (hn : 0 < n) (r : NewCellOrbit i n) :
    (newCellSplit hi n hn).symm (r, true) =
      newNonDegenerateDagger i n (newCellRepresentative i n r) := rfl

/-- Representative data uniform in the dimension, with the freeness condition only when positive. -/
structure CellReps {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (n : ℕ) where
  R : Type u
  rep : R → NewNonDegenerate i n
  cover (σ : NewNonDegenerate i n) :
    ∃ r, σ = rep r ∨ σ = newNonDegenerateDagger i n (rep r)
  separated (r s : R) :
    (rep r = rep s ∨ rep r = newNonDegenerateDagger i n (rep s)) → r = s
  nonfixed : 0 < n → ∀ r, newNonDegenerateDagger i n (rep r) ≠ rep r

/-- The chosen cells: individual vertices in degree zero, orbit representatives otherwise. -/
noncomputable def cellReps {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) : CellReps i n := by
  cases n with
  | zero =>
      exact
        { R := NewNonDegenerate i 0
          rep := id
          cover σ := ⟨σ, Or.inl rfl⟩
          separated r s h := h.elim id (fun h ↦ h.trans (newNonDegenerateDagger_zero i s))
          nonfixed hn := False.elim ((Nat.lt_irrefl 0) hn) }
  | succ n =>
      exact
        { R := NewCellOrbit i (n + 1)
          rep := newCellRepresentative i (n + 1)
          cover := newCellRepresentative_cover i (n + 1)
          separated _ _ := newCellRepresentative_separated i (n + 1)
          nonfixed hn r := newNonDegenerateDagger_ne hi hn _ }

@[simp] theorem cellReps_zero_R {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) : (cellReps hi 0).R = NewNonDegenerate i 0 := rfl

@[simp] theorem cellReps_zero_rep {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (σ : NewNonDegenerate i 0) : (cellReps hi 0).rep σ = σ := rfl

@[simp] theorem cellReps_succ_R {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) : (cellReps hi (n + 1)).R = NewCellOrbit i (n + 1) := rfl

@[simp] theorem cellReps_succ_rep {X Y : DaggerSSet.{u}} {i : X ⟶ Y}
    (hi : FreeCofibration i) (n : ℕ) (r : NewCellOrbit i (n + 1)) :
    (cellReps hi (n + 1)).rep r = newCellRepresentative i (n + 1) r := rfl

theorem CellReps.rep_injective {X Y : DaggerSSet.{u}} {i : X ⟶ Y} {n : ℕ}
    (c : CellReps i n) : Function.Injective c.rep :=
  fun r s h ↦ c.separated r s (Or.inl h)

/-- Chosen positive cells never equal the dagger of any chosen cell, including their own. -/
theorem CellReps.rep_ne_dagger_rep {X Y : DaggerSSet.{u}} {i : X ⟶ Y} {n : ℕ}
    (c : CellReps i n) (hn : 0 < n) (r s : c.R) :
    c.rep r ≠ newNonDegenerateDagger i n (c.rep s) := by
  intro h
  obtain rfl := c.separated r s (Or.inr h)
  exact c.nonfixed hn r h.symm

end DaggerModels.DaggerSSet
