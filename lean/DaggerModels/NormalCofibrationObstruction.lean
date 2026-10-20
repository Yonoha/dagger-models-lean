import DaggerModels.SimplicialSet

/-!
# The fixed-vertex obstruction to normal cofibrations

This formalizes the explicit cofibration obstruction used in
`pointset.cor.cofibrant-obstruction` and the second half of Theorem D.
The anti-involutive and dagger model structures and their Kan-extension
adjunctions are not assumed or constructed in this module.
-/

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels

/-- Reversal with an involution in all degrees, without the fixed-vertex condition. -/
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

/-- Normality requires freeness on the new nondegenerate simplices in every degree. -/
def NormalMono {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) : Prop :=
  Mono f.hom ∧ ∀ (n : ℕ) (x : Y.toSSet _⦋n⦌),
    x ∈ Y.toSSet.nonDegenerate n →
    x ∉ Set.range (f.hom.app (op ⦋n⦌)) → Y.daggerSimplex x ≠ x

end AntiInvolutiveSSet

namespace DaggerSSet

/-- Inclusion as anti-involutive simplicial sets, preserving the entire simplicial set. -/
def toAntiInvolutive : DaggerSSet.{u} ⥤ AntiInvolutiveSSet.{u} where
  obj X := ⟨X.toSSet, X.dagger, X.involutive⟩
  map f := ⟨f.hom, f.comm⟩

/-- A fixed vertex missing from the image prevents normality. -/
theorem not_normalMono_of_missing_vertex {X Y : DaggerSSet.{u}} (f : X ⟶ Y)
    (y : Y.toSSet _⦋0⦌) (hy : y ∉ Set.range (f.hom.app (op ⦋0⦌))) :
    ¬ AntiInvolutiveSSet.NormalMono (toAntiInvolutive.map f) := by
  intro h
  have hn : y ∈ Y.toSSet.nonDegenerate 0 := by simp [SSet.nondegenerate_zero]
  exact h.2 0 y hn hy (Y.dagger_vertex y)

/-- The empty dagger simplicial set. -/
def empty : DaggerSSet.{u} where
  toSSet := (Functor.const _).obj PEmpty.{u + 1}
  dagger := { app := fun _ x ↦ PEmpty.elim x }
  involutive _ x := PEmpty.elim x
  fixedVertices x := PEmpty.elim x

/-- The one-point dagger simplicial set, with its unique reversal. -/
def point : DaggerSSet.{u} where
  toSSet := (Functor.const _).obj PUnit.{u + 1}
  dagger := { app := fun _ _ ↦ PUnit.unit }
  involutive _ x := by cases x; rfl
  fixedVertices x := by cases x; rfl

def emptyToPoint : empty.{u} ⟶ point.{u} where
  hom := { app := fun _ x ↦ PEmpty.elim x }
  comm := by ext n x; exact PEmpty.elim x

/-- The empty construction has the actual categorical initial-object property. -/
def emptyIsInitial : Limits.IsInitial empty.{u} :=
  Limits.IsInitial.ofUniqueHom
    (fun X ↦
      { hom := { app := fun _ x ↦ PEmpty.elim x
                 naturality := by intro A B f; funext x; exact PEmpty.elim x }
        comm := by ext n x; exact PEmpty.elim x })
    (by intro X f; apply Hom.ext; ext n x; exact PEmpty.elim x)

/-- The point construction has the actual categorical terminal-object property. -/
def pointIsTerminal : Limits.IsTerminal point.{u} :=
  Limits.IsTerminal.ofUniqueHom
    (fun X ↦
      { hom := { app := fun _ _ ↦ PUnit.unit }
        comm := by ext n x; rfl })
    (by
      intro X f
      apply Hom.ext
      ext n x
      exact @Subsingleton.elim PUnit.{u + 1} inferInstance _ _)

instance : Mono emptyToPoint.{u} where
  right_cancellation := by
    intro Z f g _
    apply Hom.ext
    ext n x
    exact PEmpty.elim (f.hom.app n x)

/-- Every positive-dimensional simplex of the point is degenerate. -/
theorem point_degenerate {n : ℕ} (hn : 0 < n) (x : point.{u}.toSSet _⦋n⦌) :
    x ∈ point.toSSet.degenerate n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := point.toSSet.σ_mem_degenerate (0 : Fin (m + 1)) PUnit.unit
  simpa using h

/-- The initial-to-point map satisfies precisely the paper's free-cofibration condition. -/
theorem emptyToPoint_freeCofibration : FreeCofibration emptyToPoint.{u} := by
  refine ⟨inferInstance, ?_⟩
  intro n hn x hx _
  exact False.elim (hx (point_degenerate hn x))

/-- Its underlying anti-involutive map fails normality already at the unique vertex. -/
theorem emptyToPoint_not_normalMono :
    ¬ AntiInvolutiveSSet.NormalMono (toAntiInvolutive.map emptyToPoint.{u}) := by
  apply not_normalMono_of_missing_vertex emptyToPoint PUnit.unit
  rintro ⟨x, _⟩
  exact PEmpty.elim x

/-- The explicit free-cofibration and normal-monomorphism classes differ.
The witness is the actual initial-to-terminal map constructed above. -/
theorem exists_freeCofibration_not_normalMono :
    ∃ (X Y : DaggerSSet.{u}) (f : X ⟶ Y),
      FreeCofibration f ∧ ¬ AntiInvolutiveSSet.NormalMono (toAntiInvolutive.map f) :=
  ⟨empty, point, emptyToPoint, emptyToPoint_freeCofibration,
    emptyToPoint_not_normalMono⟩

end DaggerSSet
end DaggerModels
