import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Dagger simplicial sets

The definitions follow `def.dagger_simplicial_sets` and `dj.def.free-cof`
in Part I. We prove the elementary reversal and nondegeneracy lemmas
used in the proof of `dj.lem.free-cof`. The cellular characterization
of free cofibrations and the model structures are not asserted here.
-/

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels

/-- A simplicial set with a strict reversal involution fixing its vertices. -/
structure DaggerSSet where
  toSSet : SSet.{u}
  dagger : toSSet ⟶ toSSet.op
  involutive (n : ℕ) (x : toSSet _⦋n⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋n⦌)
      (SSet.opObjEquiv (dagger.app (op ⦋n⦌) x))) = x
  fixedVertices (x : toSSet _⦋0⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋0⦌) x) = x

namespace DaggerSSet

/-- The underlying involution on simplices of a fixed dimension. -/
def daggerSimplex (X : DaggerSSet.{u}) {n : ℕ} (x : X.toSSet _⦋n⦌) :
    X.toSSet _⦋n⦌ :=
  SSet.opObjEquiv (X.dagger.app (op ⦋n⦌) x)

@[simp] theorem dagger_dagger (X : DaggerSSet.{u}) {n : ℕ}
    (x : X.toSSet _⦋n⦌) : X.daggerSimplex (X.daggerSimplex x) = x :=
  X.involutive n x

@[simp] theorem dagger_vertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    X.daggerSimplex x = x := X.fixedVertices x

theorem dagger_map (X : DaggerSSet.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.toSSet.map f.op x) =
      X.toSSet.map (SimplexCategory.rev.map f).op (X.daggerSimplex x) := by
  simpa [daggerSimplex, SSet.op_map, SSet.opObjEquiv] using
    congrFun (X.dagger.naturality f.op) x

theorem dagger_δ (X : DaggerSSet.{u}) {n : ℕ}
    (i : Fin (n + 2)) (x : X.toSSet _⦋n + 1⦌) :
    X.daggerSimplex (X.toSSet.δ i x) =
      X.toSSet.δ i.rev (X.daggerSimplex x) := by
  simpa [SimplicialObject.δ] using X.dagger_map (SimplexCategory.δ i) x

theorem dagger_σ (X : DaggerSSet.{u}) {n : ℕ}
    (i : Fin (n + 1)) (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.toSSet.σ i x) =
      X.toSSet.σ i.rev (X.daggerSimplex x) := by
  simpa [SimplicialObject.σ] using X.dagger_map (SimplexCategory.σ i) x

/-- A self-conjugate edge has equal endpoints. -/
theorem selfConjugate_edge_endpoints (X : DaggerSSet.{u})
    (e : X.toSSet _⦋1⦌) (h : X.daggerSimplex e = e) :
    X.toSSet.δ 0 e = X.toSSet.δ 1 e := by
  simpa [h] using X.dagger_δ (0 : Fin 2) e

theorem dagger_mem_degenerate (X : DaggerSSet.{u}) {n : ℕ}
    {x : X.toSSet _⦋n⦌} (hx : x ∈ X.toSSet.degenerate n) :
    X.daggerSimplex x ∈ X.toSSet.degenerate n := by
  obtain ⟨m, hm, f, y, rfl⟩ := hx
  exact ⟨m, hm, SimplexCategory.rev.map f, X.daggerSimplex y,
    (X.dagger_map f y).symm⟩

@[simp] theorem dagger_mem_degenerate_iff (X : DaggerSSet.{u}) {n : ℕ}
    (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex x ∈ X.toSSet.degenerate n ↔ x ∈ X.toSSet.degenerate n := by
  constructor
  · intro hx
    simpa using X.dagger_mem_degenerate hx
  · exact X.dagger_mem_degenerate

@[simp] theorem dagger_mem_nonDegenerate_iff (X : DaggerSSet.{u}) {n : ℕ}
    (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex x ∈ X.toSSet.nonDegenerate n ↔
      x ∈ X.toSSet.nonDegenerate n := by
  simp [SSet.nonDegenerate]

/-- Dagger restricts to an involutive bijection on nondegenerate simplices. -/
def nonDegenerateEquiv (X : DaggerSSet.{u}) (n : ℕ) :
    X.toSSet.nonDegenerate n ≃ X.toSSet.nonDegenerate n where
  toFun x := ⟨X.daggerSimplex (n := n) x.1,
    (X.dagger_mem_nonDegenerate_iff (n := n) x.1).2 x.property⟩
  invFun x := ⟨X.daggerSimplex (n := n) x.1,
    (X.dagger_mem_nonDegenerate_iff (n := n) x.1).2 x.property⟩
  left_inv x := by apply Subtype.ext; exact X.dagger_dagger (n := n) x.1
  right_inv x := by apply Subtype.ext; exact X.dagger_dagger (n := n) x.1

/-- Simplicial maps commuting with the chosen reversal involutions. -/
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

/-- The forgetful functor to simplicial sets. -/
def forget : DaggerSSet.{u} ⥤ SSet.{u} where
  obj X := X.toSSet
  map f := f.hom

instance : forget.{u}.Faithful where
  map_injective h := Hom.ext h

/-- The explicit free-cofibration condition from `dj.def.free-cof`.
The equivalence with the generated cellular class is a future theorem. -/
def FreeCofibration {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=
  Mono f ∧ ∀ (n : ℕ), 0 < n → ∀ (x : Y.toSSet _⦋n⦌),
    x ∈ Y.toSSet.nonDegenerate n →
    x ∉ Set.range (f.hom.app (op ⦋n⦌)) → Y.daggerSimplex x ≠ x

end DaggerSSet
end DaggerModels
