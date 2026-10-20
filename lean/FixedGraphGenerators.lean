import FixedGraphPlacements
import FixedGraphGeometric
import Mathlib.CategoryTheory.MorphismProperty.IsSmall

/-! Literal generating families in the original fixed-object dagger graph category.
The lifting classes are the original homwise Kan and geometric weak-equivalence classes.
No model structure on graphs is assumed. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open DaggerFixedGraph DaggerFixedGraphPlacements
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFixedGraphGenerators

noncomputable section

variable (O : Type u)

/-- A single off-diagonal factor or a single original diagonal object. -/
abbrev Position := UpperIndex O ⊕ O

def placement : Position O → SSet.{u} ⥤ FixedDaggerSimplicialGraph O
  | .inl p => upperPlacement O p
  | .inr x => diagonalPlacement O x

def positionEval : Position O → FixedDaggerSimplicialGraph O ⥤ SSet.{u}
  | .inl p => homEval O p.val.1 p.val.2
  | .inr x => homEval O x x

def placementAdjunction (s : Position O) : placement O s ⊣ positionEval O s := by
  cases s with
  | inl p => exact upperAdjunction O p
  | inr x => exact diagonalAdjunction O x

/-- All ordinary boundary dimensions, including zero, in every actual factor. -/
def I : MorphismProperty (FixedDaggerSimplicialGraph O) :=
  .ofHoms (fun k : Position O × ℕ ↦ (placement O k.1).map (SSet.boundary.{u} k.2).ι)

/-- All positive-dimensional horns, placed in the same factors. -/
def J : MorphismProperty (FixedDaggerSimplicialGraph O) :=
  .ofHoms (fun k : Position O × (Σ n : ℕ, Fin (n + 2)) ↦
    (placement O k.1).map (SSet.horn.{u} (k.2.1 + 1) k.2.2).ι)

/-- Kan fibrations on every original ordered pair, including the diagonals. -/
def F : MorphismProperty (FixedDaggerSimplicialGraph O) :=
  fun _ _ f ↦ ∀ x y : O, Fibration (f.map x y)

/-- The existing geometric weak equivalence on every original Hom space. -/
def W : MorphismProperty (FixedDaggerSimplicialGraph O) :=
  fun _ _ f ↦ ∀ x y : O, WeakEquivalence (f.map x y)

theorem boundary_mem_I (s : Position O) (n : ℕ) :
    I O ((placement O s).map (SSet.boundary.{u} n).ι) := .mk (s, n)

theorem horn_mem_J (s : Position O) (n : ℕ) (i : Fin (n + 2)) :
    J O ((placement O s).map (SSet.horn.{u} (n + 1) i).ι) := by
  exact MorphismProperty.ofHoms.mk
    (f := fun k : Position O × (Σ m : ℕ, Fin (m + 2)) ↦
      (placement O k.1).map (SSet.horn.{u} (k.2.1 + 1) k.2.2).ι) (s, ⟨n, i⟩)

variable {O}

/-- Selected factor tests are exactly the tests on all original Hom spaces. -/
theorem position_property_iff_all_homs (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (∀ s : Position O, P ((positionEval O s).map f)) ↔ ∀ x y : O, P (f.map x y) := by
  constructor
  · intro h
    apply (fixedObject_homwise_iff_factors P f).2
    exact ⟨fun p ↦ h (.inl p), fun x ↦ h (.inr x)⟩
  · intro h s
    cases s with
    | inl p => exact h p.val.1 p.val.2
    | inr x => exact h x x

/-- Actual boundary lifting, without a projective-model-structure premise. -/
theorem I_rlp_iff {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (I O).rlp f ↔
      ∀ s : Position O, trivialFibrations SSet.{u} ((positionEval O s).map f) := by
  constructor
  · intro h s
    rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
    rintro K L i ⟨n⟩
    exact ((placementAdjunction O s).hasLiftingProperty_iff _ f).1
      (h _ (boundary_mem_I O s n))
  · intro h
    rintro G' H' i ⟨⟨s, n⟩⟩
    have hs := h s
    rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations] at hs
    exact ((placementAdjunction O s).hasLiftingProperty_iff _ f).2 (hs _ (.mk n))

/-- Actual horn lifting, retaining every positive-dimensional horn. -/
theorem J_rlp_iff {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (J O).rlp f ↔ ∀ s : Position O, fibrations SSet.{u} ((positionEval O s).map f) := by
  constructor
  · intro h s
    rw [SSet.modelCategoryQuillen.fibrations_eq]
    rintro K L i hi
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨i⟩⟩ := hi
    exact ((placementAdjunction O s).hasLiftingProperty_iff _ f).1
      (h _ (horn_mem_J O s n i))
  · intro h
    rintro G' H' i ⟨⟨s, n, k⟩⟩
    have hs := h s
    rw [SSet.modelCategoryQuillen.fibrations_eq] at hs
    exact ((placementAdjunction O s).hasLiftingProperty_iff _ f).2
      (hs _ (SSet.modelCategoryQuillen.horn_ι_mem_J n k))

variable (O)

theorem J_rlp_eq : (J O).rlp = F O := by
  ext G H f
  rw [J_rlp_iff, position_property_iff_all_homs]
  simp only [F, HomotopicalAlgebra.fibration_iff]

theorem I_rlp_eq : (I O).rlp = F O ⊓ W O := by
  ext G H f
  rw [I_rlp_iff, position_property_iff_all_homs]
  change (∀ x y : O, trivialFibrations SSet.{u} (f.map x y)) ↔
    (∀ x y : O, Fibration (f.map x y)) ∧ ∀ x y : O, WeakEquivalence (f.map x y)
  simp only [mem_trivialFibrations_iff]
  exact ⟨fun h ↦ ⟨fun x y ↦ (h x y).1, fun x y ↦ (h x y).2⟩,
    fun h x y ↦ ⟨h.1 x y, h.2 x y⟩⟩

theorem I_rlp_le_J_rlp : (I O).rlp ≤ (J O).rlp := by
  rw [I_rlp_eq, J_rlp_eq]
  exact inf_le_left

theorem I_rlp_iff_W_of_J_rlp {G H : FixedDaggerSimplicialGraph O}
    (f : G ⟶ H) (hf : (J O).rlp f) : (I O).rlp f ↔ W O f := by
  rw [J_rlp_eq] at hf
  rw [I_rlp_eq]
  exact and_iff_right hf

/-- This class uses realization and the singular Kan complex, including for non-Kan inputs. -/
theorem W_iff_geometric {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    W O f ↔ ∀ x y : O,
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map x y))) := by
  simp only [W, KanQuillenReuse.weakEquivalence_iff_geometric]

theorem I_isSmall : MorphismProperty.IsSmall.{u} (I O) := by
  unfold I
  infer_instance

theorem J_isSmall : MorphismProperty.IsSmall.{u} (J O) := by
  unfold J
  infer_instance

theorem placement_finitelyPresentable (s : Position O) (K : SSet.{u}) [K.Finite] :
    IsFinitelyPresentable.{u} ((placement O s).obj K) := by
  cases s with
  | inl p => exact upperPlacement_finitelyPresentable O p K
  | inr x => exact diagonalPlacement_finitelyPresentable O x K

theorem I_domain_isFinitelyPresentable {G H : FixedDaggerSimplicialGraph O}
    (i : G ⟶ H) (hi : I O i) : IsFinitelyPresentable.{u} G := by
  cases hi with
  | mk k => exact placement_finitelyPresentable O k.1 (SSet.boundary k.2)

theorem J_domain_isFinitelyPresentable {G H : FixedDaggerSimplicialGraph O}
    (i : G ⟶ H) (hi : J O i) : IsFinitelyPresentable.{u} G := by
  cases hi with
  | mk k => exact placement_finitelyPresentable O k.1 (SSet.horn (k.2.1 + 1) k.2.2)

end

end DaggerFixedGraphGenerators
