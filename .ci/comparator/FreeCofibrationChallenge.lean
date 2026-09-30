import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! Part I `dj.def.free-cof`: monicity and elementary closure, not cell generation. -/
set_option warningAsError false
open CategoryTheory Simplicial Opposite
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

theorem mono_iff_mono_hom {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom := by sorry
theorem freeCofibration_id (X : DaggerSSet.{u}) : FreeCofibration (𝟙 X) := by sorry
theorem FreeCofibration.comp {X Y Z : DaggerSSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : FreeCofibration f) (hg : FreeCofibration g) : FreeCofibration (f ≫ g) := by sorry
theorem FreeCofibration.of_retract {X Y Z W : DaggerSSet.{u}}
    {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
    (hg : FreeCofibration g) : FreeCofibration f := by sorry
theorem forget_preservesLimits : Limits.PreservesLimits forget.{u} := by sorry
theorem forget_preservesColimits : Limits.PreservesColimits forget.{u} := by sorry
theorem FreeCofibration.of_isPushout {A B C P : DaggerSSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {j : B ⟶ P} {k : C ⟶ P}
    (sq : IsPushout i f j k) (hi : FreeCofibration i) :
    FreeCofibration k := by sorry

theorem FreeCofibration.of_coproduct {I : Type u} {X Y : I → DaggerSSet.{u}}
    {P Q : DaggerSSet.{u}} (j : ∀ i, X i ⟶ P) (k : ∀ i, Y i ⟶ Q)
    (hj : Limits.IsColimit (Limits.Cofan.mk P j))
    (hk : Limits.IsColimit (Limits.Cofan.mk Q k))
    (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, FreeCofibration (f i))
    (g : P ⟶ Q) (h : ∀ i, j i ≫ g = f i ≫ k i) : FreeCofibration g := by sorry
theorem FreeCofibration.sigma_map {I : Type u} {X Y : I → DaggerSSet.{u}}
    [Limits.HasCoproduct X] [Limits.HasCoproduct Y] (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, FreeCofibration (f i)) : FreeCofibration (Limits.Sigma.map f) := by sorry
theorem forget_reflectsIsomorphisms : forget.{u}.ReflectsIsomorphisms := by sorry
theorem forget_reflectsColimits : Limits.ReflectsColimits forget.{u} := by sorry

theorem FreeCofibration.of_transfiniteCompositionOfShape {J : Type u} [LinearOrder J]
    [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (h : MorphismProperty.TransfiniteCompositionOfShape
      (fun _ _ f ↦ FreeCofibration f) J f) : FreeCofibration f := by sorry
abbrev freeCofibrations : MorphismProperty DaggerSSet.{u} :=
  fun _ _ f ↦ FreeCofibration f
theorem freeCofibrations_saturated :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} freeCofibrations.{u}).pushouts).retracts =
        freeCofibrations.{u} := by sorry

end DaggerSSet
end DaggerModels
