import OriginalCounitRightConeQCofaceImageIntersectionReconciled
import Mathlib.Data.Finset.Sort

/-!
# Explicit common old face of two distinct right-cone cofaces

For two different cofaces of `cone (n + 2)`, their old/base simplex
faces meet in the simplex on all old vertices except the two omitted
indices. This module constructs the corresponding actual simplex
morphism `⦋n⦌ ⟶ ⦋n + 2⦌` by increasing enumeration. Appending the
terminal vertex will give the large-simplex common face.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerOriginalCounitRightConeQCommonBaseFace

noncomputable section

private theorem pair_complement_card (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) :
    ({i, j}ᶜ : Finset (Fin (n + 3))).card = n + 1 := by
  rw [Finset.card_compl, Finset.card_pair hij]
  simp

/-- Increasing enumeration of the old vertices omitted by neither
coface. -/
def commonBaseOrderIso (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    Fin (n + 1) ≃o ({i, j}ᶜ : Finset (Fin (n + 3))) :=
  Finset.orderIsoOfFin _ (pair_complement_card n i j hij)

/-- The simplex map for the common old face of two distinct cofaces. -/
def commonBaseHom (n : ℕ) (i j : Fin (n + 3)) (hij : i ≠ j) :
    ⦋n⦌ ⟶ ⦋n + 2⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun v => (commonBaseOrderIso n i j hij v).1
      monotone' := by
        intro a b hab
        exact (commonBaseOrderIso n i j hij).monotone hab }

/-- Its vertex image is exactly the complement of the two indices. -/
theorem commonBaseHom_vertex_range (n : ℕ) (i j : Fin (n + 3))
    (hij : i ≠ j) (v : Fin (n + 3)) :
    v ∈ Set.range (commonBaseHom n i j hij).toOrderHom ↔
      v ≠ i ∧ v ≠ j := by
  let e := commonBaseOrderIso n i j hij
  constructor
  · rintro ⟨w, rfl⟩
    have hw : (e w).1 ∈ ({i, j}ᶜ : Finset (Fin (n + 3))) := (e w).2
    simpa only [Finset.mem_compl, Finset.mem_insert,
      Finset.mem_singleton, not_or] using hw
  · rintro ⟨hvi, hvj⟩
    have hv : v ∈ ({i, j}ᶜ : Finset (Fin (n + 3))) := by
      simp [hvi, hvj]
    obtain ⟨w, hw⟩ := e.surjective ⟨v, hv⟩
    exact ⟨w, congrArg Subtype.val hw⟩

end

end DaggerOriginalCounitRightConeQCommonBaseFace
