import DaggerModels.TwoObjectCellLifting
import DaggerModels.DaggerDiscreteObjects
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-! The actual generator family I† in Part I `bg.def.IJ` and its complete
boundary-RLP characterization within `bg.lem.I-inj`. Dimension zero is included.
The conclusion is object surjectivity and boundary lifting on each hom space;
no weak-equivalence structure or trivial-Kan/model-category conclusion is assumed. -/

open CategoryTheory

universe u

namespace DaggerModels.DaggerGeneratingCofibrations

/-- All actual free two-object boundary cell maps, including n = 0. -/
def boundaryGenerators : MorphismProperty DaggerSimplicialCat.{u, u} :=
  .ofHoms (fun n : ℕ ↦ TwoObjectDaggerCell.functor.map (SSet.boundary.{u} n).ι)

/-- The actual empty-to-identity-only-point map, as a singleton generator family. -/
def objectGenerators : MorphismProperty DaggerSimplicialCat.{u, u} :=
  .ofHoms (fun _ : Unit ↦ DaggerDiscreteObjects.emptyToPoint.{u, u})

/-- The manuscript's I† is the union of boundary cells and the object generator. -/
def generators : MorphismProperty DaggerSimplicialCat.{u, u} :=
  boundaryGenerators ⊔ objectGenerators

variable {C D : DaggerSimplicialCat.{u, u}} (p : C ⟶ D)

/-- Boundary-cell lifting is precisely boundary lifting on every full hom space. -/
theorem boundary_rlp_iff : boundaryGenerators.rlp p ↔
    ∀ (x y : C.Obj) (n : ℕ), HasLiftingProperty (SSet.boundary.{u} n).ι (p.map x y) := by
  constructor
  · intro hp x y n
    exact (TwoObjectCellLifting.hasLiftingProperty_iff _ p).1 (hp _ (.mk n)) x y
  · intro hp A B f hf
    cases hf with
    | mk n => exact (TwoObjectCellLifting.hasLiftingProperty_iff _ p).2 (fun x y ↦ hp x y n)

/-- Lifting against the singleton object family is exactly object surjectivity. -/
theorem object_rlp_iff : objectGenerators.rlp p ↔ Function.Surjective p.obj := by
  constructor
  · intro hp
    exact (DaggerDiscreteObjects.hasLiftingProperty_iff_surjective p).1
      (hp _ (.mk Unit.unit))
  · intro hp A B f hf
    cases hf with
    | mk _ => exact (DaggerDiscreteObjects.hasLiftingProperty_iff_surjective p).2 hp

/-- The full I† right-lifting condition, without a model-category assertion. -/
theorem generators_rlp_iff : generators.rlp p ↔
    Function.Surjective p.obj ∧
      ∀ (x y : C.Obj) (n : ℕ), HasLiftingProperty (SSet.boundary.{u} n).ι (p.map x y) := by
  constructor
  · intro hp
    have ho : objectGenerators.rlp p := by
      intro A B f hf
      exact hp f (Or.inr hf)
    have hb : boundaryGenerators.rlp p := by
      intro A B f hf
      exact hp f (Or.inl hf)
    exact ⟨(object_rlp_iff p).1 ho, (boundary_rlp_iff p).1 hb⟩
  · rintro ⟨ho, hb⟩ A B f hf
    change boundaryGenerators f ∨ objectGenerators f at hf
    rcases hf with hf | hf
    · exact (boundary_rlp_iff p).2 hb f hf
    · exact (object_rlp_iff p).2 ho f hf

end DaggerModels.DaggerGeneratingCofibrations
