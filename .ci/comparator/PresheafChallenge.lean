import Mathlib.AlgebraicTopology.SimplicialSet.Op
import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-! Part I `prop.sSetdag_is_equivalent_to_Fun`: an actual equivalence of categories. -/
set_option warningAsError false
open CategoryTheory Simplicial Opposite
open CategoryTheory.Limits
universe u
namespace DaggerModels

structure ReverseSimplex where
  len : ℕ
namespace ReverseSimplex
structure Hom (m n : ReverseSimplex) where
  toFun : Fin (m.len + 1) → Fin (n.len + 1)
  monotone_or_antitone : Monotone toFun ∨ Antitone toFun
instance {m n : ReverseSimplex} : CoeFun (Hom m n)
    (fun _ => Fin (m.len + 1) → Fin (n.len + 1)) := ⟨Hom.toFun⟩
@[ext] theorem Hom.ext {m n : ReverseSimplex} {f g : Hom m n}
    (h : ∀ i, f i = g i) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      cases hfg
      rfl
def Hom.id (m : ReverseSimplex) : Hom m m :=
  ⟨fun i => i, Or.inl (fun _ _ h => h)⟩
def Hom.comp {m n p : ReverseSimplex} (f : Hom m n) (g : Hom n p) : Hom m p where
  toFun i := g (f i)
  monotone_or_antitone := by
    rcases f.monotone_or_antitone with hf | hf <;>
      rcases g.monotone_or_antitone with hg | hg
    · exact Or.inl (fun _ _ h => hg (hf h))
    · exact Or.inr (fun _ _ h => hg (hf h))
    · exact Or.inr (fun _ _ h => hg (hf h))
    · exact Or.inl (fun _ _ h => hg (hf h))
instance : SmallCategory ReverseSimplex where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext; intro i; rfl
  comp_id f := by apply Hom.ext; intro i; rfl
  assoc f g h := by apply Hom.ext; intro i; rfl
end ReverseSimplex

structure DaggerSSet where
  toSSet : SSet.{u}
  dagger : toSSet ⟶ toSSet.op
  involutive (n : ℕ) (x : toSSet _⦋n⦌) :
    SSet.opObjEquiv (dagger.app (op ⦋n⦌)
      (SSet.opObjEquiv (dagger.app (op ⦋n⦌) x))) = x
  fixedVertices (x : toSSet _⦋0⦌) : SSet.opObjEquiv (dagger.app (op ⦋0⦌) x) = x
namespace DaggerSSet
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
end DaggerSSet

theorem nonempty_daggerSSetEquivalencePresheaf :
    Nonempty (DaggerSSet.{u} ≌ (ReverseSimplexᵒᵖ ⥤ Type u)) := by sorry

theorem daggerSSetHasLimits : HasLimits DaggerSSet.{u} := by sorry
theorem daggerSSetHasColimits : HasColimits DaggerSSet.{u} := by sorry
theorem daggerSSetLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} DaggerSSet.{u} := by sorry
theorem daggerSSetLocallyPresentable : IsLocallyPresentable.{u} DaggerSSet.{u} := by sorry

theorem exists_freeDaggerAdjunction :
    ∃ F : SSet.{u} ⥤ DaggerSSet.{u}, Nonempty (F ⊣ DaggerSSet.forget.{u}) := by sorry

end DaggerModels
