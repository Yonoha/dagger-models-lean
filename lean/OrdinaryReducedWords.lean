import OrdinaryWordBoundary
import DaggerModels.SimplicialEnrichment

/-! Right actions on the original alternating words and their degreewise reduced subset.
The complement of the boundary is used only degreewise; simplex operators can reduce length. -/

open CategoryTheory MonoidalCategory DaggerModels
open DaggerOrdinaryWordBoundary

universe u

namespace DaggerOrdinaryReducedWords

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) (L : SSet.{u})

/-- Compose an original old arrow into the last old factor, keeping every new letter. -/
def appendOld (q : SimplexCategoryᵒᵖ) : (n : ℕ) → (a b c : C.Obj) →
    (Word C x y L n a b).obj q → (b ⟶[SSet] c).obj q → (Word C x y L n a c).obj q
  | 0, a, b, c, w, h => (eComp SSet a b c).app q (w, h)
  | n + 1, _, b, c, w, h => (w.1, appendOld q n y b c w.2 h)

/-- Append a new original letter and the original identity at its target. -/
def appendNew (q : SimplexCategoryᵒᵖ) : (n : ℕ) → (a : C.Obj) →
    (Word C x y L n a x).obj q → L.obj q → (Word C x y L (n + 1) a y).obj q
  | 0, _, w, l => ((w, l), (eId SSet y).app q PUnit.unit)
  | n + 1, _, w, l => (w.1, appendNew q n y w.2 l)

theorem appendOld_id (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b : C.Obj)
    (w : (Word C x y L n a b).obj q) :
    appendOld C x y L q n a b b w ((eId SSet b).app q PUnit.unit) = w := by
  induction n generalizing a with
  | zero => exact Category.comp_id (obj := SimplicialEnrichment.At C.Obj q) w
  | succ n ih =>
    change (w.1, appendOld C x y L q n y b b w.2 _) = w
    rw [ih]
    rfl

theorem appendOld_assoc (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b c d : C.Obj)
    (w : (Word C x y L n a b).obj q)
    (h : (b ⟶[SSet] c).obj q) (k : (c ⟶[SSet] d).obj q) :
    appendOld C x y L q n a c d (appendOld C x y L q n a b c w h) k =
      appendOld C x y L q n a b d w ((eComp SSet b c d).app q (h, k)) := by
  induction n generalizing a with
  | zero => exact Category.assoc (obj := SimplicialEnrichment.At C.Obj q) w h k
  | succ n ih =>
    change (w.1, appendOld C x y L q n y c d (appendOld C x y L q n y b c w.2 h) k) = _
    rw [ih]
    rfl

theorem appendOld_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    (n : ℕ) (a b c : C.Obj) (w : (Word C x y L n a b).obj q)
    (h : (b ⟶[SSet] c).obj q) :
    (Word C x y L n a c).map α (appendOld C x y L q n a b c w h) =
      appendOld C x y L q' n a b c ((Word C x y L n a b).map α w)
        ((b ⟶[SSet] c).map α h) := by
  induction n generalizing a with
  | zero => exact (SimplicialEnrichment.map C.Obj α).map_comp w h
  | succ n ih =>
    apply Prod.ext
    · rfl
    · exact ih y w.2

theorem appendNew_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    (n : ℕ) (a : C.Obj) (w : (Word C x y L n a x).obj q) (l : L.obj q) :
    (Word C x y L (n + 1) a y).map α (appendNew C x y L q n a w l) =
      appendNew C x y L q' n a ((Word C x y L n a x).map α w) (L.map α l) := by
  induction n generalizing a with
  | zero =>
    apply Prod.ext
    · rfl
    · exact (SimplicialEnrichment.map C.Obj α).map_id y
  | succ n ih =>
    apply Prod.ext
    · rfl
    · exact ih y w.2

variable {L} (K : L.Subcomplex)

theorem appendOld_mem_boundary (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b c : C.Obj)
    (w : (Word C x y L n a b).obj q) (h : (b ⟶[SSet] c).obj q) :
    appendOld C x y L q n a b c w h ∈ (Boundary C x y K n a c).obj q ↔
      w ∈ (Boundary C x y K n a b).obj q := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [mem_boundary_succ, appendOld, ih]

theorem appendNew_mem_boundary (q : SimplexCategoryᵒᵖ) (n : ℕ) (a : C.Obj)
    (w : (Word C x y L n a x).obj q) (l : L.obj q) :
    appendNew C x y L q n a w l ∈ (Boundary C x y K (n + 1) a y).obj q ↔
      w ∈ (Boundary C x y K n a x).obj q ∨ l ∈ K.obj q := by
  induction n generalizing a with
  | zero =>
    rw [mem_boundary_succ]
    change (_ ∨ False) ↔ (False ∨ _)
    simp only [appendNew, or_false, false_or]
  | succ n ih =>
    simp only [mem_boundary_succ, appendNew, ih, or_assoc]

/-- Exact original words outside their boundary, with their number of new letters. -/
def Reduced (q : SimplexCategoryᵒᵖ) (a b : C.Obj) :=
  Σ n : ℕ, {w : (Word C x y L n a b).obj q // w ∉ (Boundary C x y K n a b).obj q}

def old (q : SimplexCategoryᵒᵖ) {a b : C.Obj} (h : (a ⟶[SSet] b).obj q) :
    Reduced C x y K q a b := ⟨0, h, by intro h; exact h⟩

def rightOld (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (w : Reduced C x y K q a b) (h : (b ⟶[SSet] c).obj q) : Reduced C x y K q a c :=
  ⟨w.1, appendOld C x y L q w.1 a b c w.2.val h, fun hm ↦
    w.2.property ((appendOld_mem_boundary C x y K q w.1 a b c w.2.val h).1 hm)⟩

def rightNew (q : SimplexCategoryᵒᵖ) {a : C.Obj}
    (w : Reduced C x y K q a x) (l : L.obj q) (hl : l ∉ K.obj q) :
    Reduced C x y K q a y :=
  ⟨w.1 + 1, appendNew C x y L q w.1 a w.2.val l, fun hm ↦
    ((appendNew_mem_boundary C x y K q w.1 a w.2.val l).1 hm).elim w.2.property hl⟩

theorem rightOld_id (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (w : Reduced C x y K q a b) :
    rightOld C x y K q w ((eId SSet b).app q PUnit.unit) = w := by
  cases w with
  | mk n w =>
    apply congrArg (Sigma.mk n)
    apply Subtype.ext
    exact appendOld_id C x y L q n a b w.val

theorem rightOld_assoc (q : SimplexCategoryᵒᵖ) {a b c d : C.Obj}
    (w : Reduced C x y K q a b) (h : (b ⟶[SSet] c).obj q) (k : (c ⟶[SSet] d).obj q) :
    rightOld C x y K q (rightOld C x y K q w h) k =
      rightOld C x y K q w ((eComp SSet b c d).app q (h, k)) := by
  apply congrArg (Sigma.mk w.1)
  apply Subtype.ext
  exact appendOld_assoc C x y L q w.1 a b c d w.2.val h k

theorem old_injective (q : SimplexCategoryᵒᵖ) (a b : C.Obj) :
    Function.Injective (old C x y K q (a := a) (b := b)) := by
  intro h k hk
  exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp hk).2)

end

end DaggerOrdinaryReducedWords
