import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.AlgebraicTopology.SimplexCategory.Rev
import Mathlib.CategoryTheory.Whiskering

/-!
# Parameter reversal on the actual topological standard simplices

This is the natural parameter comparison needed for realizing a dagger.
It does not regard an anti-simplicial dagger as a simplicial self-map.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace DaggerOriginalTopologicalSimplexReversal

noncomputable section

/-- Pushforward along the actual reversal of the finite vertex set. -/
def reverse (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) → stdSimplex ℝ (Fin (n + 1)) :=
  stdSimplex.map Fin.rev

/-- Parameter reversal is involutive. -/
theorem reverse_reverse (n : ℕ) (x : stdSimplex ℝ (Fin (n + 1))) :
    reverse n (reverse n x) = x := by
  unfold reverse
  rw [stdSimplex.map_comp_apply]
  have h : (Fin.rev : Fin (n + 1) → Fin (n + 1)).comp Fin.rev = id := by
    funext i
    exact Fin.rev_rev i
  rw [h, stdSimplex.map_id_apply]

/-- Reversal conjugates the actual simplex map to the reversed simplex operator. -/
theorem reverse_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (x : stdSimplex ℝ (Fin (n.len + 1))) :
    reverse m.len (stdSimplex.map (SimplexCategory.rev.map f) x) =
      stdSimplex.map f (reverse n.len x) := by
  unfold reverse
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  congr 1
  funext i
  change ((SimplexCategory.rev.map f).toOrderHom i).rev = f.toOrderHom i.rev
  rw [SimplexCategory.rev_map_apply, Fin.rev_rev]
  rfl

/-- The standard zero-simplex is pointwise fixed under parameter reversal. -/
theorem reverse_zero (x : stdSimplex ℝ (Fin 1)) : reverse 0 x = x := by
  unfold reverse
  have h : (Fin.rev : Fin 1 → Fin 1) = id := by
    funext i
    exact Subsingleton.elim _ _
  rw [h, stdSimplex.map_id_apply]

/-- The parameter reversal is an isomorphism of the actual topological simplex. -/
def simplexIso (n : SimplexCategory) :
    SimplexCategory.toTop₀.obj n ≅ SimplexCategory.toTop₀.obj n where
  hom := TopCat.ofHom ⟨reverse n.len, stdSimplex.continuous_map Fin.rev⟩
  inv := TopCat.ofHom ⟨reverse n.len, stdSimplex.continuous_map Fin.rev⟩
  hom_inv_id := by
    ext x
    exact reverse_reverse n.len x
  inv_hom_id := by
    ext x
    exact reverse_reverse n.len x

/-- Naturality is on the original covariant reversal of the simplex category. -/
def reversalIso₀ :
    SimplexCategory.rev ⋙ SimplexCategory.toTop₀ ≅ SimplexCategory.toTop₀ :=
  NatIso.ofComponents simplexIso (by
    intro n m f
    ext x
    exact reverse_naturality f x)

/-- The same comparison in the original universe-polymorphic realization diagram. -/
def reversalIso :
    SimplexCategory.rev ⋙ SimplexCategory.toTop.{u} ≅ SimplexCategory.toTop.{u} :=
  (Functor.associator SimplexCategory.rev SimplexCategory.toTop₀
    TopCat.uliftFunctor).symm ≪≫ Functor.isoWhiskerRight reversalIso₀ TopCat.uliftFunctor

/-- The lifted component is exactly coordinate reversal on its underlying simplex. -/
theorem reversalIso_hom_apply (n : SimplexCategory)
    (x : SimplexCategory.toTop.{u}.obj n) :
    ((reversalIso.{u}.hom.app n) x).down = reverse n.len x.down := rfl

/-- Double reversal coherence holds on the actual lifted components. -/
theorem reversalIso_hom_sq (n : SimplexCategory) :
    reversalIso.{u}.hom.app n ≫ reversalIso.{u}.hom.app n =
      𝟙 (SimplexCategory.toTop.{u}.obj n) := by
  ext x
  apply ULift.ext
  exact reverse_reverse n.len x.down

end

end DaggerOriginalTopologicalSimplexReversal
