import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-! Part I `dj.lem.free-cof`: actual relative skeleta, source, inclusions, and colimit. -/
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
def IsDaggerStable {X : DaggerSSet.{u}} (K : X.toSSet.Subcomplex) : Prop :=
  ∀ (n : ℕ) (x : X.toSSet _⦋n⦌), x ∈ K.obj (op ⦋n⦌) →
    X.daggerSimplex x ∈ K.obj (op ⦋n⦌)
theorem daggerStable_range {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    IsDaggerStable (SSet.Subcomplex.range f.hom) := by sorry
theorem daggerStable_skeleton (X : DaggerSSet.{u}) (n : ℕ) :
    IsDaggerStable (X.toSSet.skeleton n) := by sorry
-- Mathlib uses dimension < n, so stage 0 is the image and stage n+1 is B_{≤n}.
theorem exists_relativeSkeletonFiltration {X Y : DaggerSSet.{u}} (i : X ⟶ Y) [Mono i] :
    ∃ t : TransfiniteCompositionOfShape ℕ i, ∀ n,
      ∃ e : (t.F.obj n).toSSet ≅
          (SSet.Subcomplex.range i.hom ⊔ Y.toSSet.skeleton n).toSSet,
        e.hom ≫ (SSet.Subcomplex.range i.hom ⊔ Y.toSSet.skeleton n).ι =
          (t.incl.app n).hom := by sorry

end DaggerSSet
end DaggerModels
