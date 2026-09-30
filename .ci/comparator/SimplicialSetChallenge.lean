import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-! Trusted specification: dagger simplicial sets, ten results and three definition roots. -/
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

@[simp] theorem dagger_dagger (X : DaggerSSet.{u}) {n : ℕ} (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.daggerSimplex x) = x := by sorry
@[simp] theorem dagger_vertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    X.daggerSimplex x = x := by sorry
theorem dagger_map (X : DaggerSSet.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.toSSet.map f.op x) =
      X.toSSet.map (SimplexCategory.rev.map f).op (X.daggerSimplex x) := by sorry
theorem dagger_δ (X : DaggerSSet.{u}) {n : ℕ} (i : Fin (n + 2)) (x : X.toSSet _⦋n + 1⦌) :
    X.daggerSimplex (X.toSSet.δ i x) = X.toSSet.δ i.rev (X.daggerSimplex x) := by sorry
theorem dagger_σ (X : DaggerSSet.{u}) {n : ℕ} (i : Fin (n + 1)) (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.toSSet.σ i x) = X.toSSet.σ i.rev (X.daggerSimplex x) := by sorry
theorem selfConjugate_edge_endpoints (X : DaggerSSet.{u})
    (e : X.toSSet _⦋1⦌) (h : X.daggerSimplex e = e) :
    X.toSSet.δ 0 e = X.toSSet.δ 1 e := by sorry
theorem dagger_mem_degenerate (X : DaggerSSet.{u}) {n : ℕ}
    {x : X.toSSet _⦋n⦌} (hx : x ∈ X.toSSet.degenerate n) :
    X.daggerSimplex x ∈ X.toSSet.degenerate n := by sorry
@[simp] theorem dagger_mem_degenerate_iff (X : DaggerSSet.{u}) {n : ℕ} (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex x ∈ X.toSSet.degenerate n ↔ x ∈ X.toSSet.degenerate n := by sorry
@[simp] theorem dagger_mem_nonDegenerate_iff (X : DaggerSSet.{u}) {n : ℕ}
    (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex x ∈ X.toSSet.nonDegenerate n ↔
      x ∈ X.toSSet.nonDegenerate n := by sorry

def nonDegenerateEquiv (X : DaggerSSet.{u}) (n : ℕ) :
    X.toSSet.nonDegenerate n ≃ X.toSSet.nonDegenerate n where
  toFun x := ⟨X.daggerSimplex (n := n) x.1,
    (X.dagger_mem_nonDegenerate_iff (n := n) x.1).2 x.property⟩
  invFun x := ⟨X.daggerSimplex (n := n) x.1,
    (X.dagger_mem_nonDegenerate_iff (n := n) x.1).2 x.property⟩
  left_inv x := by apply Subtype.ext; exact X.dagger_dagger (n := n) x.1
  right_inv x := by apply Subtype.ext; exact X.dagger_dagger (n := n) x.1

structure Hom (X Y : DaggerSSet.{u}) where
  hom : X.toSSet ⟶ Y.toSSet
  comm : hom ≫ Y.dagger = X.dagger ≫ SSet.opFunctor.map hom

@[ext] theorem Hom.ext {X Y : DaggerSSet.{u}} {f g : Hom X Y}
    (h : f.hom = g.hom) : f = g := by sorry

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

end DaggerSSet
end DaggerModels

namespace DaggerModels.ComparatorContracts
universe audit_u

theorem freeCofibration_definition {X Y : DaggerSSet.{audit_u}} (f : X ⟶ Y) :
    DaggerSSet.FreeCofibration f ↔ DaggerSSet.FreeCofibration f := by sorry
theorem nonDegenerateEquiv_definition (X : DaggerSSet.{audit_u}) (n : ℕ) :
    X.nonDegenerateEquiv n = X.nonDegenerateEquiv n := by sorry
theorem forget_definition : DaggerSSet.forget.{audit_u} = DaggerSSet.forget.{audit_u} := by sorry

end DaggerModels.ComparatorContracts
