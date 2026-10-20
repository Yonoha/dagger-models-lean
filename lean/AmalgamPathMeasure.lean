import AmalgamGraph
import Mathlib.Logic.Relation

/-! Count the literal second-factor letters in the original colored paths.
No normal form, alternative relation, or simplicial complement is introduced. -/

open CategoryTheory MonoidalCategory DaggerModels DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamPathMeasure

noncomputable section

set_option autoImplicit false

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

/-- Count actual true-tag edges, retaining every original endpoint and simplex. -/
def rightCount (q : SimplexCategoryᵒᵖ) {a z : Objects B B' b b'} :
    Path B B' b b' q a z → ℕ
  | .nil => 0
  | .cons p e => rightCount q p + (if e.val.1 then 1 else 0)

@[simp] theorem rightCount_nil (q : SimplexCategoryᵒᵖ) (a : Objects B B' b b') :
    rightCount B B' b b' q (Quiver.Path.nil : Path B B' b b' q a a) = 0 := rfl

@[simp] theorem rightCount_cons (q : SimplexCategoryᵒᵖ) {a y z : Objects B B' b b'}
    (p : Path B B' b b' q a y) (e : (graphHom B B' b b' y z).obj q) :
    rightCount B B' b b' q (p.cons e) =
      rightCount B B' b b' q p + (if e.val.1 then 1 else 0) := rfl

@[simp] theorem rightCount_singleton (q : SimplexCategoryᵒᵖ)
    {a z : Objects B B' b b'} (e : (graphHom B B' b b' a z).obj q) :
    rightCount B B' b b' q (Quiver.Path.nil.cons e) =
      (if e.val.1 then 1 else 0) := Nat.zero_add _

@[simp] theorem rightCount_factorPath (c : Bool) (q : SimplexCategoryᵒᵖ)
    {x y : (factor B B' c).Obj} (h : (x ⟶[SSet] y).obj q) :
    rightCount B B' b b' q (factorPath B B' b b' c q h) =
      (if c then 1 else 0) := by
  cases c <;> rfl

@[simp] theorem rightCount_comp (q : SimplexCategoryᵒᵖ)
    {a y z : Objects B B' b b'} (p : Path B B' b b' q a y)
    (s : Path B B' b b' q y z) :
    rightCount B B' b b' q (p.comp s) =
      rightCount B B' b b' q p + rightCount B B' b b' q s := by
  induction s with
  | nil => rfl
  | cons s e ih =>
    change rightCount B B' b b' q (p.comp s) + (if e.val.1 then 1 else 0) = _
    rw [ih, Nat.add_assoc]
    rfl

/-- Every ordinary simplex operator preserves the literal color count. -/
@[simp] theorem rightCount_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects B B' b b'} (p : Path B B' b b' q a z) :
    rightCount B B' b b' q' (SimplicialColimitsFree.Paths.map _ α p) =
      rightCount B B' b b' q p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change rightCount B B' b b' q' (SimplicialColimitsFree.Paths.map _ α p) +
      (if e.val.1 then 1 else 0) = rightCount B B' b b' q p + _
    rw [ih]

/-- A deleted true-tag identity contributes one; a false-tag identity contributes zero. -/
theorem rightCount_factorId_delta (c : Bool) (q : SimplexCategoryᵒᵖ)
    (x : (factor B B' c).Obj) :
    rightCount B B' b b' q (factorPath B B' b b' c q ((eId SSet x).app q PUnit.unit)) =
      rightCount B B' b b' q (Quiver.Path.nil : Path B B' b b' q
        (label B B' b b' c x) (label B B' b b' c x)) + (if c then 1 else 0) := by
  rw [rightCount_factorPath, rightCount_nil, Nat.zero_add]

/-- The composite remains one original letter, even when it is an identity. -/
theorem rightCount_factorComp_delta (c : Bool) (q : SimplexCategoryᵒᵖ)
    {x y z : (factor B B' c).Obj} (h : (x ⟶[SSet] y).obj q)
    (k : (y ⟶[SSet] z).obj q) :
    rightCount B B' b b' q
      ((factorPath B B' b b' c q h).comp (factorPath B B' b b' c q k)) =
      rightCount B B' b b' q
        (factorPath B B' b b' c q ((eComp SSet x y z).app q (h, k))) +
          (if c then 1 else 0) := by
  rw [rightCount_comp, rightCount_factorPath, rightCount_factorPath,
    rightCount_factorPath]

theorem rightCount_rel_le {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    {p p' : Path B B' b b' q a z} (h : Rel B B' b b' q a z p p') :
    rightCount B B' b b' q p' ≤ rightCount B B' b b' q p := by
  cases h with
  | factorId c x =>
    rw [rightCount_factorPath, rightCount_nil]
    exact Nat.zero_le _
  | factorComp c h k =>
    rw [rightCount_comp, rightCount_factorPath, rightCount_factorPath,
      rightCount_factorPath]
    exact Nat.le_add_right _ _

/-- Nonincrease for exactly the original relation closed under both path contexts. -/
theorem rightCount_compClosure_le {q : SimplexCategoryᵒᵖ}
    {a z : Objects B B' b b'} {p p' : Path B B' b b' q a z}
    (h : HomRel.CompClosure (SimplicialCat.HomQuotient.degreeRel
      (relations B B' b b') q) p p') :
    rightCount B B' b b' q p' ≤ rightCount B B' b b' q p := by
  rcases h with ⟨x, y, f, m, m', g, h⟩
  change rightCount B B' b b' q (f.comp (m'.comp g)) ≤
    rightCount B B' b b' q (f.comp (m.comp g))
  simp only [rightCount_comp]
  exact Nat.add_le_add_left
    (Nat.add_le_add_right (rightCount_rel_le B B' b b' h) _) _

/-- Finite original contextual reductions never increase the true-tag count. -/
theorem rightCount_reflTransGen_le {q : SimplexCategoryᵒᵖ}
    {a z : Objects B B' b b'} {p p' : Path B B' b b' q a z}
    (h : Relation.ReflTransGen (fun p₁ p₂ : Path B B' b b' q a z ↦
      HomRel.CompClosure (SimplicialCat.HomQuotient.degreeRel
        (relations B B' b b') q) p₁ p₂) p p') :
    rightCount B B' b b' q p' ≤ rightCount B B' b b' q p := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h hstep ih =>
    exact (rightCount_compClosure_le B B' b b' hstep).trans ih

end
end DaggerAmalgamPathMeasure
