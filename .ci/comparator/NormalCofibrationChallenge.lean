import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-! The explicit cofibration obstruction for Part I Theorem D; no model structure assumed. -/
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
def FreeCofibration {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=
  Mono f ∧ ∀ (n : ℕ), 0 < n → ∀ (x : Y.toSSet _⦋n⦌),
    x ∈ Y.toSSet.nonDegenerate n →
    x ∉ Set.range (f.hom.app (op ⦋n⦌)) → Y.daggerSimplex x ≠ x
end DaggerSSet

structure AntiInvolutiveSSet where
  toSSet : SSet.{u}
  dagger : toSSet ⟶ toSSet.op
  involutive (n : ℕ) (x : toSSet _⦋n⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋n⦌)
      (SSet.opObjEquiv (dagger.app (op ⦋n⦌) x))) = x
namespace AntiInvolutiveSSet
def daggerSimplex (X : AntiInvolutiveSSet.{u}) {n : ℕ} (x : X.toSSet _⦋n⦌) :
    X.toSSet _⦋n⦌ := SSet.opObjEquiv (X.dagger.app (op ⦋n⦌) x)
structure Hom (X Y : AntiInvolutiveSSet.{u}) where
  hom : X.toSSet ⟶ Y.toSSet
  comm : hom ≫ Y.dagger = X.dagger ≫ SSet.opFunctor.map hom
@[ext] theorem Hom.ext {X Y : AntiInvolutiveSSet.{u}} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl
instance : Category AntiInvolutiveSSet.{u} where
  Hom := Hom
  id X := ⟨𝟙 X.toSSet, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    rw [Category.assoc, g.comm, ← Category.assoc, f.comm,
      Category.assoc, Functor.map_comp]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f g h := by apply Hom.ext; simp [Category.assoc]
def NormalMono {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) : Prop :=
  Mono f.hom ∧ ∀ (n : ℕ) (x : Y.toSSet _⦋n⦌),
    x ∈ Y.toSSet.nonDegenerate n →
    x ∉ Set.range (f.hom.app (op ⦋n⦌)) → Y.daggerSimplex x ≠ x
end AntiInvolutiveSSet

namespace DaggerSSet
def toAntiInvolutive : DaggerSSet.{u} ⥤ AntiInvolutiveSSet.{u} where
  obj X := ⟨X.toSSet, X.dagger, X.involutive⟩
  map f := ⟨f.hom, f.comm⟩
theorem not_normalMono_of_missing_vertex {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (y : Y.toSSet _⦋0⦌) (hy : y ∉ Set.range (f.hom.app (op ⦋0⦌))) :
    ¬ AntiInvolutiveSSet.NormalMono (toAntiInvolutive.map f) := by sorry
theorem exists_freeCofibration_not_normalMono :
    ∃ (X Y : DaggerSSet.{u}) (f : X ⟶ Y),
      FreeCofibration f ∧ ¬ AntiInvolutiveSSet.NormalMono (toAntiInvolutive.map f) := by sorry
end DaggerSSet
end DaggerModels
