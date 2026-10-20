import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-!
# The reversal simplex category

The category used in Part I has actual monotone or antitone functions as
morphisms. In particular, a constant function has only one representation
as a morphism. This is not the tagged category from the appendix.
The presheaf equivalence is proved in `DaggerModels.Presheaf`.
-/

open CategoryTheory

namespace DaggerModels

/-- Objects of the reversal simplex category are nonempty finite ordinals. -/
structure ReverseSimplex where
  len : ℕ

namespace ReverseSimplex

/-- Morphisms carry an orientation property, not a choice of orientation. -/
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

/-- The usual reversal of a finite ordinal. -/
def reversal (n : ReverseSimplex) : n ⟶ n where
  toFun := Fin.rev
  monotone_or_antitone := Or.inr (fun _ _ h => by simpa using h)

@[simp] theorem reversal_apply (n : ReverseSimplex) (i : Fin (n.len + 1)) :
    (reversal n).toFun i = i.rev := rfl

@[simp] theorem reversal_comp_reversal (n : ReverseSimplex) :
    reversal n ≫ reversal n = 𝟙 n := by
  apply Hom.ext
  intro i
  exact Fin.rev_rev i

theorem reversal_zero : reversal ⟨0⟩ = 𝟙 (ReverseSimplex.mk 0) := by
  apply Hom.ext
  intro i
  change (i : Fin 1).rev = i
  apply Fin.ext
  have hi := i.isLt
  change i.val < 1 at hi
  simp only [Fin.val_rev]
  omega

/-- The inclusion of the usual simplex category. -/
def inclusion : SimplexCategory ⥤ ReverseSimplex where
  obj n := ⟨n.len⟩
  map f := ⟨f.toOrderHom, Or.inl f.toOrderHom.monotone⟩
  map_id n := by apply Hom.ext; intro i; rfl
  map_comp f g := by apply Hom.ext; intro i; rfl

theorem reversal_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    inclusion.map f ≫ reversal (inclusion.obj n) =
      reversal (inclusion.obj m) ≫ inclusion.map (SimplexCategory.rev.map f) := by
  apply Hom.ext
  intro i
  change (f.toOrderHom i).rev = (f.toOrderHom i.rev.rev).rev
  rw [Fin.rev_rev]

/-- Precisely the constant maps admit both orientation properties. -/
theorem monotone_antitone_iff_constant {m n : ReverseSimplex}
    (f : Fin (m.len + 1) → Fin (n.len + 1)) :
    Monotone f ∧ Antitone f ↔ ∀ i j, f i = f j := by
  constructor
  · rintro ⟨hm, ha⟩ i j
    rcases le_total i j with h | h
    · exact le_antisymm (hm h) (ha h)
    · exact le_antisymm (ha h) (hm h)
  · intro h
    exact ⟨fun i j _ => le_of_eq (h i j), fun i j _ => le_of_eq (h j i)⟩

end ReverseSimplex
end DaggerModels
