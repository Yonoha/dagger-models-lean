import FixedCategoryAdjunction
import FixedGraphStructural
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! Literal free-image generators and their exact lifting classes on fixed-O dagger categories.
The original free adjunction and graph classes are reused. No category model structure,
free-cell acyclicity, finite-presentable free domains or factorization is assumed here.
-/

open CategoryTheory HomotopicalAlgebra DaggerModels DaggerFixedCategoryAdjunction
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFixedCategoryGenerators

noncomputable section

variable (O : Type u)

/-- The literal free images of every original placed boundary, including dimension zero. -/
def I : MorphismProperty (FixedDaggerSimplicialCat O) :=
  .ofHoms (fun k : DaggerFixedGraphGenerators.Position O × ℕ ↦
    (free O).map ((DaggerFixedGraphGenerators.placement O k.1).map (SSet.boundary.{u} k.2).ι))

/-- The literal free images of all positive horns at the same original positions. -/
def J : MorphismProperty (FixedDaggerSimplicialCat O) :=
  .ofHoms (fun k : DaggerFixedGraphGenerators.Position O × (Σ n : ℕ, Fin (n + 2)) ↦
    (free O).map
      ((DaggerFixedGraphGenerators.placement O k.1).map (SSet.horn.{u} (k.2.1 + 1) k.2.2).ι))

def W : MorphismProperty (FixedDaggerSimplicialCat O) :=
  (DaggerFixedGraphGenerators.W O).inverseImage (FixedDaggerSimplicialCat.forgetGraph O)

def F : MorphismProperty (FixedDaggerSimplicialCat O) :=
  (DaggerFixedGraphGenerators.F O).inverseImage (FixedDaggerSimplicialCat.forgetGraph O)

theorem boundary_mem_I (s : DaggerFixedGraphGenerators.Position O) (n : ℕ) :
    I O ((free O).map
      ((DaggerFixedGraphGenerators.placement O s).map (SSet.boundary.{u} n).ι)) := .mk (s, n)

theorem horn_mem_J (s : DaggerFixedGraphGenerators.Position O) (n : ℕ) (i : Fin (n + 2)) :
    J O ((free O).map
      ((DaggerFixedGraphGenerators.placement O s).map (SSet.horn.{u} (n + 1) i).ι)) := by
  exact MorphismProperty.ofHoms.mk
    (f := fun k : DaggerFixedGraphGenerators.Position O × (Σ m : ℕ, Fin (m + 2)) ↦
      (free O).map ((DaggerFixedGraphGenerators.placement O k.1).map
        (SSet.horn.{u} (k.2.1 + 1) k.2.2).ι)) (s, ⟨n, i⟩)

variable {O}

/-- Every full original Hom map is retained by the identity-object adapter. -/
theorem original_hom_property_iff (P : MorphismProperty SSet.{u})
    {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) (x y : O) :
    P (((FixedDaggerSimplicialCat.forgetGraph O).map f).map x y) ↔ P (f.val.map x y) := by
  rcases f with ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩
  cases h
  rfl

theorem W_iff_homwise {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    W O f ↔ ∀ x y : O, WeakEquivalence (f.val.map x y) := by
  change (∀ x y, WeakEquivalence
    (((FixedDaggerSimplicialCat.forgetGraph O).map f).map x y)) ↔ _
  simp only [weakEquivalence_iff]
  exact forall₂_congr (fun x y ↦ original_hom_property_iff (weakEquivalences SSet.{u}) f x y)

theorem F_iff_homwise {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    F O f ↔ ∀ x y : O, Fibration (f.val.map x y) := by
  change (∀ x y, Fibration
    (((FixedDaggerSimplicialCat.forgetGraph O).map f).map x y)) ↔ _
  simp only [fibration_iff]
  exact forall₂_congr (fun x y ↦ original_hom_property_iff (fibrations SSet.{u}) f x y)

/-- The weak equivalence uses realization and singular Kan, with no Kan-input premise. -/
theorem W_iff_geometric {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    W O f ↔ ∀ x y : O,
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.val.map x y))) := by
  rw [W_iff_homwise]
  simp only [KanQuillenReuse.weakEquivalence_iff_geometric]

/-- The actual adjunction transports each literal boundary lifting problem. -/
theorem I_rlp_iff_graph {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    (I O).rlp f ↔
      (DaggerFixedGraphGenerators.I O).rlp ((FixedDaggerSimplicialCat.forgetGraph O).map f) := by
  constructor
  · intro h
    rintro G H i ⟨k⟩
    exact ((adjunction O).hasLiftingProperty_iff _ f).1 (h _ (.mk k))
  · intro h
    rintro C' D' i ⟨k⟩
    exact ((adjunction O).hasLiftingProperty_iff _ f).2 (h _ (.mk k))

/-- All original positive horn lifting problems are transported by the same adjunction. -/
theorem J_rlp_iff_graph {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D) :
    (J O).rlp f ↔
      (DaggerFixedGraphGenerators.J O).rlp ((FixedDaggerSimplicialCat.forgetGraph O).map f) := by
  constructor
  · intro h
    rintro G H i ⟨k⟩
    exact ((adjunction O).hasLiftingProperty_iff _ f).1 (h _ (.mk k))
  · intro h
    rintro C' D' i ⟨k⟩
    exact ((adjunction O).hasLiftingProperty_iff _ f).2 (h _ (.mk k))

variable (O)

theorem I_rlp_eq : (I O).rlp = F O ⊓ W O := by
  ext C D f
  rw [I_rlp_iff_graph, DaggerFixedGraphGenerators.I_rlp_eq]
  rfl

theorem J_rlp_eq : (J O).rlp = F O := by
  ext C D f
  rw [J_rlp_iff_graph, DaggerFixedGraphGenerators.J_rlp_eq]
  rfl

theorem I_rlp_le_J_rlp : (I O).rlp ≤ (J O).rlp := by
  rw [I_rlp_eq, J_rlp_eq]
  exact inf_le_left

theorem I_rlp_iff_W_of_J_rlp {C D : FixedDaggerSimplicialCat O}
    (f : C ⟶ D) (hf : (J O).rlp f) : (I O).rlp f ↔ W O f := by
  rw [J_rlp_eq] at hf
  rw [I_rlp_eq]
  exact and_iff_right hf

theorem I_isSmall : MorphismProperty.IsSmall.{u} (I O) := by
  unfold I
  infer_instance

theorem J_isSmall : MorphismProperty.IsSmall.{u} (J O) := by
  unfold J
  infer_instance

instance W_twoOutOfThree : (W O).HasTwoOutOfThreeProperty := by
  unfold W
  infer_instance

instance W_retracts : (W O).IsStableUnderRetracts := by
  unfold W
  infer_instance

end

end DaggerFixedCategoryGenerators
