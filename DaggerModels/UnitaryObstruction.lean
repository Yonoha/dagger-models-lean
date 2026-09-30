import DaggerModels.DaggerCategory
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Int.Basic

/-!
# The integer dagger-groupoid obstruction

This implements the ordinary dagger-groupoid example in Part I,
`pointset.prop.weak-counterexample`: its fully faithful dagger inclusion is an ordinary
equivalence but is not unitarily essentially surjective. These are parts (1) and (2) of the
example, also used in `pointset.thm.generator-comparison`.

The claims about dagger nerves, DCH weak equivalences, dagger Joyal equivalences and the
failure of Quillen adjunctions are not proved in this file.
-/

open CategoryTheory

namespace DaggerModels.UnitaryObstruction

/-- The two objects, represented by `false` and `true`. The type synonym keeps the
integer groupoid structure separate from any other category structure on `Bool`. -/
def IntegerGroupoid := Bool

namespace IntegerGroupoid

def zero : IntegerGroupoid := false

def one : IntegerGroupoid := true

instance : DecidableEq IntegerGroupoid := inferInstanceAs (DecidableEq Bool)

instance : SmallGroupoid IntegerGroupoid where
  Hom _ _ := ℤ
  id _ := 0
  comp a b := a + b
  id_comp a := Int.zero_add a
  comp_id a := Int.add_zero a
  assoc a b c := Int.add_assoc a b c
  inv a := -a
  inv_comp a := by omega
  comp_inv a := by omega

/-- The integer representing a morphism; the hom type itself is definitionally `ℤ`. -/
def label {i j : IntegerGroupoid} (a : i ⟶ j) : ℤ := a

/-- The integer offsets are $t_0 = 0$ and $t_1 = 1$. -/
def shift : IntegerGroupoid → ℤ
  | false => 0
  | true => 1

instance : DaggerCategory IntegerGroupoid where
  dagger {i j} a := label a + shift i - shift j
  dagger_involutive {i j} a := by
    change label a + shift i - shift j + shift j - shift i = label a
    omega
  dagger_id i := by change 0 + shift i - shift i = 0; omega
  dagger_comp {i j k} a b := by
    change label a + label b + shift i - shift k =
      (label b + shift j - shift k) + (label a + shift i - shift j)
    omega

@[simp] theorem id_eq_zero (i : IntegerGroupoid) : (𝟙 i : i ⟶ i) = (0 : ℤ) := rfl

@[simp] theorem comp_eq_add {i j k : IntegerGroupoid} (a : i ⟶ j) (b : j ⟶ k) :
    a ≫ b = (label a + label b : ℤ) := rfl

@[simp] theorem inverse_eq_neg {i j : IntegerGroupoid} (a : i ⟶ j) :
    Groupoid.inv a = (-label a : ℤ) := rfl

@[simp] theorem dagger_eq {i j : IntegerGroupoid} (a : i ⟶ j) :
    dagger a = (label a + shift i - shift j : ℤ) := rfl

/-- The unitary equations reduce to the exact integer equation in the manuscript. -/
theorem isUnitary_iff {i j : IntegerGroupoid} (a : i ⟶ j) :
    IsUnitary a ↔ 2 * label a = shift j - shift i := by
  change (label a + (label a + shift i - shift j) = 0 ∧
    (label a + shift i - shift j) + label a = 0) ↔ _
  omega

/-- No unitary morphism connects the two distinct objects. -/
theorem not_isUnitary_of_ne {i j : IntegerGroupoid} (hij : i ≠ j) (a : i ⟶ j) :
    ¬ IsUnitary a := by
  rw [isUnitary_iff]
  cases i with
  | false =>
    cases j with
    | false => exact (hij rfl).elim
    | true =>
      change ¬ 2 * label a = (1 : ℤ)
      omega
  | true =>
    cases j with
    | false =>
      change ¬ 2 * label a = (-1 : ℤ)
      omega
    | true => exact (hij rfl).elim

/-- A unitary endomorphism is precisely the identity. -/
theorem isUnitary_endomorphism_iff (i : IntegerGroupoid) (a : i ⟶ i) :
    IsUnitary a ↔ a = 𝟙 i := by
  rw [isUnitary_iff]
  change 2 * label a = shift i - shift i ↔ label a = (0 : ℤ)
  omega

/-- The zero-labelled morphisms give ordinary isomorphisms between every pair of objects. -/
def zeroIso (i j : IntegerGroupoid) : i ≅ j where
  hom := (0 : ℤ)
  inv := (0 : ℤ)
  hom_inv_id := rfl
  inv_hom_id := rfl

end IntegerGroupoid

/-- The full subgroupoid on the object represented by `false`. -/
def zeroObjects : ObjectProperty IntegerGroupoid := fun i ↦ i = false

abbrev ZeroSubgroupoid := zeroObjects.FullSubcategory

instance : Groupoid ZeroSubgroupoid :=
  Groupoid.ofFullyFaithfulToGroupoid zeroObjects.ι zeroObjects.fullyFaithfulι

/-- The unique object of the full subgroupoid. -/
def zeroObject : ZeroSubgroupoid := ⟨false, rfl⟩

/-- The standard full-subcategory inclusion. It inherits dagger preservation. -/
abbrev inclusion : ZeroSubgroupoid ⥤ IntegerGroupoid := zeroObjects.ι

/-- Full faithfulness is the actual mathlib functor property. -/
def inclusionFullyFaithful : inclusion.FullyFaithful := zeroObjects.fullyFaithfulι

instance : inclusion.EssSurj where
  mem_essImage i := ⟨zeroObject, ⟨IntegerGroupoid.zeroIso false i⟩⟩

/-- The inclusion is an ordinary equivalence of categories. -/
instance inclusionIsEquivalence : inclusion.IsEquivalence where

/-- An actual categorical equivalence with the inclusion as its forward functor. -/
noncomputable def ordinaryEquivalence : ZeroSubgroupoid ≌ IntegerGroupoid :=
  inclusion.asEquivalence

/-- The inclusion fails the unitary form of essential surjectivity at `true`. -/
theorem inclusion_not_unitarilyEssentiallySurjective :
    ¬ UnitarilyEssentiallySurjective inclusion := by
  intro h
  obtain ⟨i, a, ha⟩ := h true
  apply IntegerGroupoid.not_isUnitary_of_ne (i := i.obj) (j := true) _ a ha
  change i.obj ≠ true
  rw [i.property]
  decide

/-- The strict obstruction used after mapping into this groupoid in the generator proof. -/
theorem no_unitary_false_true
    (a : IntegerGroupoid.zero ⟶ IntegerGroupoid.one) : ¬ IsUnitary a :=
  IntegerGroupoid.not_isUnitary_of_ne
    (i := IntegerGroupoid.zero) (j := IntegerGroupoid.one) (by decide) a

/-- The source example's two ordinary-category claims, on the actual dagger inclusion.
This statement does not include the unformalized nerve and model-structure conclusions. -/
theorem inclusion_counterexample :
    DaggerFunctor inclusion ∧ inclusion.Full ∧ inclusion.Faithful ∧
      inclusion.IsEquivalence ∧ ¬ UnitarilyEssentiallySurjective inclusion :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inclusion_not_unitarilyEssentiallySurjective⟩

/-- There exist small dagger groupoids and a fully faithful dagger functor which is an
ordinary equivalence but fails unitary essential surjectivity, as in source parts (1)--(2). -/
theorem exists_equivalence_not_unitarilyEssentiallySurjective :
    ∃ (C D : Type) (gC : SmallGroupoid C) (gD : SmallGroupoid D),
      letI := gC
      letI := gD
      ∃ (dC : DaggerCategory C) (dD : DaggerCategory D),
        letI := dC
        letI := dD
        ∃ F : C ⥤ D, DaggerFunctor F ∧ F.Full ∧ F.Faithful ∧ F.IsEquivalence ∧
          ¬ UnitarilyEssentiallySurjective F := by
  refine ⟨ZeroSubgroupoid, IntegerGroupoid, inferInstance, inferInstance,
    inferInstance, inferInstance, inclusion, ?_⟩
  exact inclusion_counterexample

end DaggerModels.UnitaryObstruction
