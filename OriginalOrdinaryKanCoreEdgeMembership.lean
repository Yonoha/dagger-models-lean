import OriginalOrdinaryKanCoreNerveMembership

/-!
# Membership in the core candidate expressed by all actual simplicial edges

The categorical nerve range criterion is identified with invertibility of all
one-dimensional faces under the actual homotopy-category unit. The statement
uses all simplex operators from [1], including degenerate edges, and is valid
for arbitrary simplicial sets and arbitrary universe. No Kan property is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreNerveMembership

universe v u

namespace DaggerOriginalOrdinaryKanCoreEdgeMembership

noncomputable section

/-- The genuine simplex operator selecting any ordered pair of vertices. -/
def pairOperator {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun k ↦ if k = 0 then i else j
    monotone' := by
      intro a b hab
      by_cases ha : a = 0
      · subst a
        by_cases hb : b = 0
        · simp only [hb, ↓reduceIte, le_refl]
        · simpa only [↓reduceIte, hb] using hij
      · have hb : b ≠ 0 := by
          intro hb
          subst b
          have : a = 0 := le_antisymm hab (by
            change 0 ≤ a.val
            exact Nat.zero_le _)
          exact ha this
        simp only [ha, hb, ↓reduceIte, le_refl] }

/-- Selecting a pair in the nerve recovers the literal arrow between those two vertices. -/
theorem pairOperator_nerve_hom {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) {i j : Fin (n + 1)} (f : i ⟶ j) :
    ((nerve C).map (pairOperator i j (leOfHom f)).op s).hom = s.map f := rfl

/-- All arrows of a nerve simplex are iso exactly when all its actual 1-faces are iso. -/
theorem unit_arrows_iso_iff_edges_iso {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) :
    (∀ {i j : Fin (n + 1)} (f : i ⟶ j), IsIso (s.map f)) ↔
      ∀ α : ⦋1⦌ ⟶ ⦋n⦌, IsIso (((nerve C).map α.op s).hom) := by
  constructor
  · intro h α
    change IsIso (s.map ((SimplexCategory.toCat.map α).toFunctor.map
      (homOfLE (X := Fin 2) (show (0 : Fin 2) ≤ 1 by decide))))
    exact h _
  · intro h i j f
    have hf := h (pairOperator i j (leOfHom f))
    rwa [pairOperator_nerve_hom] at hf

/-- Invertibility of an actual edge means invertibility of its exact unit image in ho(X). -/
def edgeIsInvertible (X : SSet.{u}) (e : X.obj (op ⦋1⦌)) : Prop :=
  IsIso (((homotopyCategoryUnit X).app (op ⦋1⦌) e).hom)

/-- Exact core membership expressed using all original one-dimensional simplex faces. -/
theorem mem_ordinaryCoreCandidate_iff_edges_iso (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) (s : X.obj q) :
    s ∈ (ordinaryCoreCandidate X).obj q ↔
      ∀ α : ⦋1⦌ ⟶ q.unop, edgeIsInvertible X (X.map α.op s) := by
  rw [mem_ordinaryCoreCandidate_iff_unit_arrows_iso, unit_arrows_iso_iff_edges_iso]
  constructor
  · intro h α
    have he := h α
    have hn := congrFun ((homotopyCategoryUnit X).naturality α.op) s
    change (homotopyCategoryUnit X).app (op ⦋1⦌) (X.map α.op s) =
      (nerve (SSet.hoFunctor.obj X)).map α.op ((homotopyCategoryUnit X).app q s) at hn
    dsimp [edgeIsInvertible]
    rw [hn]
    exact he
  · intro h α
    have he := h α
    have hn := congrFun ((homotopyCategoryUnit X).naturality α.op) s
    change (homotopyCategoryUnit X).app (op ⦋1⦌) (X.map α.op s) =
      (nerve (SSet.hoFunctor.obj X)).map α.op ((homotopyCategoryUnit X).app q s) at hn
    dsimp [edgeIsInvertible] at he
    rw [hn] at he
    exact he

end

end DaggerOriginalOrdinaryKanCoreEdgeMembership
