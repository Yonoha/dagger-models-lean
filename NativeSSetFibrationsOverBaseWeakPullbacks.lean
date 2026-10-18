import TopCatModelCategory.ModelCategorySSet
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# Base change of weak equivalences between actual fibrations over the same base

An explicit relative Brown factorization keeps the same projection to the
original base. The comparison is factored through two trivial fibrations.
Their pullbacks remain trivial fibrations, so every original base-change
map is weak. No fibrancy assumption on the base or on the source of base
change is introduced, and no claim about a non-fibration is made.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSSetFibrationsOverBaseWeakPullbacks
noncomputable section

/-- The exact native base-change map for an actual map over the same base. -/
def mapOver {X Y B K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y)
    (h : f ≫ q = p) (b : K ⟶ B) : pullback p b ⟶ pullback q b :=
  pullback.lift (pullback.fst p b ≫ f) (pullback.snd p b) (by
    rw [Category.assoc, h]
    exact pullback.condition)

/-- The exact map over the base commutes with the unchanged first projection. -/
theorem mapOver_fst {X Y B K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y)
    (h : f ≫ q = p) (b : K ⟶ B) :
    mapOver p q f h b ≫ pullback.fst q b = pullback.fst p b ≫ f := by
  simp [mapOver]

/-- The actual base-change square with the original total map is a native pullback. -/
theorem mapOver_isPullback {X Y B K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ q = p) (b : K ⟶ B) :
    IsPullback (mapOver p q f h b) (pullback.fst p b) (pullback.fst q b) f := by
  have outer : IsPullback (mapOver p q f h b ≫ pullback.snd q b)
      (pullback.fst p b) b (f ≫ q) := by
    simpa [mapOver, h] using (IsPullback.of_hasPullback p b).flip
  exact outer.of_right (mapOver_fst p q f h b) (IsPullback.of_hasPullback q b).flip

/-- Relative Brown data uses the original projections and two actual trivial fibrations. -/
theorem relativeBrown {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y)
    (h : f ≫ q = p) [Fibration p] [Fibration q] [WeakEquivalence f] :
    ∃ (Z : SSet.{u}) (i : X ⟶ Z) (r : Z ⟶ X) (s : Z ⟶ Y),
      WeakEquivalence i ∧ Fibration r ∧ WeakEquivalence r ∧
        Fibration s ∧ WeakEquivalence s ∧ i ≫ r = 𝟙 X ∧ i ≫ s = f ∧ r ≫ p = s ≫ q := by
  let graph : X ⟶ pullback p q := pullback.lift (𝟙 X) f (by simpa using h.symm)
  let a := MorphismProperty.factorizationData (trivialCofibrations SSet) (fibrations SSet)
    graph
  have hi : WeakEquivalence a.i := (mem_trivialCofibrations_iff a.i).1 a.hi |>.2
  have hp : Fibration a.p := (fibration_iff a.p).2 a.hp
  let r := a.p ≫ pullback.fst p q
  let s := a.p ≫ pullback.snd p q
  have hir : a.i ≫ r = 𝟙 X := by
    dsimp only [r]
    rw [← Category.assoc, a.fac]
    simp [graph]
  have his : a.i ≫ s = f := by
    dsimp only [s]
    rw [← Category.assoc, a.fac]
    simp [graph]
  have hr : Fibration r := inferInstance
  have hs : Fibration s := inferInstance
  have hwr : WeakEquivalence r := weakEquivalence_of_precomp_of_fac hir
  have hws : WeakEquivalence s := weakEquivalence_of_precomp_of_fac his
  refine ⟨a.Z, a.i, r, s, hi, hr, hwr, hs, hws, hir, his, ?_⟩
  dsimp only [r, s]
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- Base change preserves weakness between actual fibrations over the unchanged base. -/
theorem mapOver_weakEquivalence {X Y B K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ q = p) (b : K ⟶ B)
    [Fibration p] [Fibration q] [WeakEquivalence f] :
    WeakEquivalence (mapOver p q f h b) := by
  obtain ⟨Z, i, r, s, hi, hr, hwr, hs, hws, hir, his, hrs⟩ := relativeBrown p q f h
  have := hi
  have := hr
  have := hwr
  have := hs
  have := hws
  let z := r ≫ p
  let rK := mapOver z p r rfl b
  let sK := mapOver z q s hrs.symm b
  have hrK : Fibration rK ∧ WeakEquivalence rK := by
    apply (mem_trivialFibrations_iff rK).1
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (mapOver_isPullback z p r rfl b).flip
      ((mem_trivialFibrations_iff r).2 ⟨hr, hwr⟩)
  have hsK : Fibration sK ∧ WeakEquivalence sK := by
    apply (mem_trivialFibrations_iff sK).1
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (mapOver_isPullback z q s hrs.symm b).flip
      ((mem_trivialFibrations_iff s).2 ⟨hs, hws⟩)
  have hiz : i ≫ z = p := by dsimp only [z]; rw [← Category.assoc, hir, Category.id_comp]
  let iK := mapOver p z i hiz b
  have hirK : iK ≫ rK = 𝟙 (pullback p b) := by
    apply pullback.hom_ext <;> simp [iK, rK, mapOver, hir]
  have hisK : iK ≫ sK = mapOver p q f h b := by
    apply pullback.hom_ext <;> simp [iK, sK, mapOver, his]
  have := hrK.2
  have := hsK.2
  have : WeakEquivalence iK := weakEquivalence_of_postcomp_of_fac hirK
  rw [← hisK]
  infer_instance

end
end DaggerNativeSSetFibrationsOverBaseWeakPullbacks
