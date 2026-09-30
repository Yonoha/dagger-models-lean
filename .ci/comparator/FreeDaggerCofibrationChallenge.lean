import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-! Part I `dj.cor.Fdag-free` and the full cellular characterization `dj.lem.free-cof`. -/
set_option warningAsError false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
universe u
namespace DaggerModels

structure DaggerSSet where
  toSSet : SSet.{u}
  dagger : toSSet ⟶ toSSet.op
  involutive (n : ℕ) (x : toSSet _⦋n⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋n⦌)
      (SSet.opObjEquiv (dagger.app (op ⦋n⦌) x))) = x
  fixedVertices (x : toSSet _⦋0⦌) : SSet.opObjEquiv (dagger.app (op ⦋0⦌) x) = x
namespace DaggerSSet
def daggerSimplex (X : DaggerSSet.{u}) {n : ℕ} (x : X.toSSet _⦋n⦌) : X.toSSet _⦋n⦌ :=
  SSet.opObjEquiv (X.dagger.app (op ⦋n⦌) x)
structure Hom (X Y : DaggerSSet.{u}) where
  hom : X.toSSet ⟶ Y.toSSet
  comm : hom ≫ Y.dagger = X.dagger ≫ SSet.opFunctor.map hom
@[ext] theorem Hom.ext {X Y : DaggerSSet.{u}} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl
instance : Category DaggerSSet.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.toSSet, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm,
      Category.assoc, Functor.map_comp]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; simp [Category.assoc]
def forget : DaggerSSet.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom
def FreeCofibration {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=
  Mono f ∧ ∀ (n : ℕ), 0 < n → ∀ (x : Y.toSSet _⦋n⦌),
    x ∈ Y.toSSet.nonDegenerate n →
    x ∉ Set.range (f.hom.app (op ⦋n⦌)) → Y.daggerSimplex x ≠ x

abbrev freeCofibrations : MorphismProperty DaggerSSet.{u} :=
  fun _ _ f ↦ FreeCofibration f
end DaggerSSet

theorem freeDagger_nonDegenerate_not_fixed
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    (A : SSet.{u}) (n : ℕ) (hn : 0 < n)
    (x : (F.obj A).toSSet _⦋n⦌) (hx : x ∈ (F.obj A).toSSet.nonDegenerate n) :
    (F.obj A).daggerSimplex x ≠ x := by sorry
theorem freeDagger_map_freeCofibration
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    {K L : SSet.{u}} (i : K ⟶ L) [Mono i] : DaggerSSet.FreeCofibration (F.map i) := by sorry
def freeBoundaryGenerators (F : SSet.{u} ⥤ DaggerSSet.{u}) :
    MorphismProperty DaggerSSet.{u} :=
  .ofHoms (fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι)
theorem freeBoundarySaturation_le (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators F)).pushouts).retracts ≤
        DaggerSSet.freeCofibrations := by sorry
theorem freeCofibration_of_relativeCellComplex (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) {J : Type u} [LinearOrder J]
    [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (c : RelativeCellComplex.{u}
      (fun (_ : J) ↦ fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) f) :
    DaggerSSet.FreeCofibration f := by sorry
theorem freeBoundary_rlp_iff (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget) {X Y : DaggerSSet.{u}} (p : X ⟶ Y) :
    (freeBoundaryGenerators F).rlp p ↔
      ∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p.hom := by sorry

theorem exists_relativeFreeBoundaryCellComplex
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    {X Y : DaggerSSet.{u}} (i : X ⟶ Y) (hi : DaggerSSet.FreeCofibration i) :
    Nonempty (RelativeCellComplex.{u}
      (fun (_ : ℕ) ↦ fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) i) := by sorry
theorem freeBoundarySaturation_eq
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget) :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators F)).pushouts).retracts =
        DaggerSSet.freeCofibrations := by sorry

end DaggerModels
