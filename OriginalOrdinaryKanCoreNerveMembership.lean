import OriginalOrdinaryKanCoreSubcomplex

/-!
# Nerve membership in the ordinary categorical core

Use the existing categorical core and its actual nerve inclusion. A simplex
belongs to its degreewise range exactly when all arrows of the corresponding
composable-arrow functor are isomorphisms. Apply this to the literal unit into
the nerve of the homotopy category, retaining arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex

universe v u

namespace DaggerOriginalOrdinaryKanCoreNerveMembership

noncomputable section

/-- Lift the same composable-arrow diagram to the existing core when its arrows are iso. -/
def liftComposableArrowsToCore {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n)
    (hs : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), IsIso (s.map f)) :
    ComposableArrows (Core C) n where
  obj i := Core.mk (s.obj i)
  map f := by
    have : IsIso (s.map f) := hs f
    exact ⟨asIso (s.map f)⟩
  map_id := by
    intro i
    apply Core.hom_ext
    change s.map (𝟙 i) = 𝟙 (s.obj i)
    exact s.map_id i
  map_comp := by
    intro i j k f g
    apply Core.hom_ext
    change s.map (f ≫ g) = s.map f ≫ s.map g
    exact s.map_comp f g

/-- Forgetting the lifted simplex recovers the exact original composable-arrow functor. -/
theorem liftComposableArrowsToCore_forget {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n)
    (hs : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), IsIso (s.map f)) :
    liftComposableArrowsToCore s hs ⋙ Core.inclusion C = s := by
  refine ComposableArrows.ext (fun i ↦ rfl) ?_
  intro i hi
  change s.map' i (i + 1) (by omega) hi =
    𝟙 _ ≫ s.map' i (i + 1) (by omega) hi ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

/-- Exact range membership for the native nerve of the ordinary categorical core. -/
theorem exists_nerveCoreLift_iff {C : Type u} [Category.{v} C] {n : ℕ}
    (s : ComposableArrows C n) :
    (∃ t : ComposableArrows (Core C) n,
      (nerveMap (Core.inclusion C)).app (op ⦋n⦌) t = s) ↔
      ∀ {i j : Fin (n + 1)} (f : i ⟶ j), IsIso (s.map f) := by
  constructor
  · rintro ⟨t, rfl⟩ i j f
    change IsIso ((Core.inclusion C).map (t.map f))
    infer_instance
  · intro hs
    refine ⟨liftComposableArrowsToCore s hs, ?_⟩
    exact liftComposableArrowsToCore_forget s hs

/-- The core candidate's membership is the actual invertibility predicate in ho(X). -/
theorem mem_ordinaryCoreCandidate_iff_unit_arrows_iso (X : SSet.{u})
    (q : SimplexCategoryᵒᵖ) (s : X.obj q) :
    s ∈ (ordinaryCoreCandidate X).obj q ↔
      ∀ {i j : Fin (q.unop.len + 1)} (f : i ⟶ j),
        IsIso (((homotopyCategoryUnit X).app q s).map f) := by
  rw [mem_ordinaryCoreCandidate_iff]
  exact exists_nerveCoreLift_iff ((homotopyCategoryUnit X).app q s)

end

end DaggerOriginalOrdinaryKanCoreNerveMembership
