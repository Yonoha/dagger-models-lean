import C2InvolutionBridge
import IinjBridge
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! The literal free BC₂ boundary/horn generators and their evaluation RLP bridge.
The group is the frozen `Multiplicative (ZMod 2)`, and all maps are actual functor data.
No diagram model structure or fibrancy assumption is introduced. -/

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFreeBC2

abbrev BC2 := SingleObj DaggerFixedGraph.C2

abbrev point : BC2 := PUnit.unit

noncomputable def free : SSet.{u} ⥤ (BC2 ⥤ SSet.{u}) :=
  evaluationLeftAdjoint SSet.{u} point

noncomputable def ev : (BC2 ⥤ SSet.{u}) ⥤ SSet.{u} :=
  (evaluation BC2 SSet.{u}).obj point

noncomputable def freeAdjunction : free.{u} ⊣ ev.{u} :=
  evaluationAdjunctionRight SSet.{u} point

/-- The actual underlying object is the coproduct indexed by the original C₂. -/
theorem free_obj (K : SSet.{u}) :
    (free.obj K).obj point = ∐ (fun _ : DaggerFixedGraph.C2 ↦ K) := rfl

/-- The action sends the g-summand to the h*g-summand, with SingleObj variance. -/
theorem free_action_ι (K : SSet.{u}) (g h : DaggerFixedGraph.C2) :
    Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) g ≫ (free.obj K).map (X := point) (Y := point) h =
      Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) (h * g) := by
  simp [free, evaluationLeftAdjoint, Sigma.ι_desc]
  rfl

/-- The nonidentity action sends the identity summand to the nonidentity summand. -/
theorem free_flip_one (K : SSet.{u}) :
    Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) 1 ≫
      (free.obj K).map (X := point) (Y := point) DaggerFixedGraph.flip =
        Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) DaggerFixedGraph.flip := by
  simpa using free_action_ι K 1 DaggerFixedGraph.flip

/-- The same nonidentity action sends the other summand back to the identity summand. -/
theorem free_flip_flip (K : SSet.{u}) :
    Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) DaggerFixedGraph.flip ≫
      (free.obj K).map (X := point) (Y := point) DaggerFixedGraph.flip =
        Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) 1 := by
  simpa using free_action_ι K DaggerFixedGraph.flip DaggerFixedGraph.flip

/-- The arrow component acts by the same given arrow on every C₂ summand. -/
theorem free_map_ι {K L : SSet.{u}} (f : K ⟶ L) (g : DaggerFixedGraph.C2) :
    Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) g ≫ (free.map f).app point =
      f ≫ Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ L) g := by
  simp [free, evaluationLeftAdjoint, Sigma.ι_desc]
  rfl

/-- The full underlying component is the coproduct of the two copies of the original map. -/
theorem free_map_app {K L : SSet.{u}} (f : K ⟶ L) :
    (free.map f).app point = Limits.Sigma.map (fun _ : DaggerFixedGraph.C2 ↦ f) := by
  apply Sigma.hom_ext (f := (fun _ : DaggerFixedGraph.C2 ↦ K))
  intro g
  simp [free_map_ι]

/-- Protect the actual adjunction hom equivalence, including the identity summand. -/
theorem free_homEquiv {K : SSet.{u}} {F : BC2 ⥤ SSet.{u}} (η : free.obj K ⟶ F) :
    freeAdjunction.homEquiv K F η =
      Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) 1 ≫ η.app point := rfl

/-- All boundary dimensions, including n=0, are retained as a literal family. -/
noncomputable def I : MorphismProperty (BC2 ⥤ SSet.{u}) :=
  .ofHoms (fun n : ℕ ↦ free.map (SSet.boundary.{u} n).ι)

/-- Exactly the positive-dimensional horns, with their full original index family. -/
noncomputable def J : MorphismProperty (BC2 ⥤ SSet.{u}) :=
  ⨆ n : ℕ, MorphismProperty.ofHoms
    (fun i : Fin (n + 2) ↦ free.map (SSet.horn.{u} (n + 1) i).ι)

theorem boundary_mem_I (n : ℕ) : I (free.map (SSet.boundary.{u} n).ι) := by
  exact ⟨n⟩

theorem horn_mem_J (n : ℕ) (i : Fin (n + 2)) :
    J (free.map (SSet.horn.{u} (n + 1) i).ι) := by
  simp only [J, MorphismProperty.iSup_iff]
  exact ⟨n, ⟨i⟩⟩

theorem boundary_lifting_iff_rlp {F G : BC2 ⥤ SSet.{u}} (p : F ⟶ G) :
    (∀ n : ℕ, HasLiftingProperty (free.map (SSet.boundary.{u} n).ι) p) ↔ I.rlp p := by
  constructor
  · intro h
    rintro A B f ⟨n⟩
    exact h n
  · intro h n
    exact h _ (boundary_mem_I n)

/-- Free boundary RLP is precisely ordinary trivial-fibration RLP after evaluation. -/
theorem I_rlp_eq :
    I.{u}.rlp = (trivialFibrations SSet.{u}).inverseImage ev := by
  ext F G p
  change I.rlp p ↔ trivialFibrations SSet.{u} (ev.map p)
  rw [← boundary_lifting_iff_rlp, ← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations,
    ← DaggerModels.KanQuillenReuse.boundary_lifting_iff_rlp]
  exact forall_congr' (fun n ↦ freeAdjunction.hasLiftingProperty_iff _ _)

/-- Free horn RLP is precisely ordinary Kan fibration RLP after evaluation. -/
theorem J_rlp_eq : J.{u}.rlp = (fibrations SSet.{u}).inverseImage ev := by
  ext F G p
  change J.rlp p ↔ fibrations SSet.{u} (ev.map p)
  rw [SSet.modelCategoryQuillen.fibrations_eq]
  constructor
  · intro h
    rintro A B f hf
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    exact (freeAdjunction.hasLiftingProperty_iff _ p).1 (h _ (horn_mem_J n i))
  · intro h
    rintro A B f hf
    simp only [J, MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    exact (freeAdjunction.hasLiftingProperty_iff _ p).2
      (h _ (SSet.modelCategoryQuillen.horn_ι_mem_J n i))

end DaggerFreeBC2
