import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-! Trusted specification: actual monotone-or-antitone maps, with six proof obligations. -/
set_option warningAsError false
open CategoryTheory

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
    (h : ∀ i, f i = g i) : f = g := by sorry

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

def reversal (n : ReverseSimplex) : n ⟶ n where
  toFun := Fin.rev
  monotone_or_antitone := Or.inr (fun _ _ h => by simpa using h)

@[simp] theorem reversal_apply (n : ReverseSimplex) (i : Fin (n.len + 1)) :
    (reversal n).toFun i = i.rev := by sorry

@[simp] theorem reversal_comp_reversal (n : ReverseSimplex) :
    reversal n ≫ reversal n = 𝟙 n := by sorry

theorem reversal_zero : reversal ⟨0⟩ = 𝟙 (ReverseSimplex.mk 0) := by sorry

def inclusion : SimplexCategory ⥤ ReverseSimplex where
  obj n := ⟨n.len⟩
  map f := ⟨f.toOrderHom, Or.inl f.toOrderHom.monotone⟩
  map_id n := by apply Hom.ext; intro i; rfl
  map_comp f g := by apply Hom.ext; intro i; rfl

theorem reversal_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    inclusion.map f ≫ reversal (inclusion.obj n) =
      reversal (inclusion.obj m) ≫ inclusion.map (SimplexCategory.rev.map f) := by sorry

theorem monotone_antitone_iff_constant {m n : ReverseSimplex}
    (f : Fin (m.len + 1) → Fin (n.len + 1)) :
    Monotone f ∧ Antitone f ↔ ∀ i j, f i = f j := by sorry

end ReverseSimplex
end DaggerModels
