import OriginalRestBoundaryInverseGluing

/-!
# The original inverse face-source operator is the actual remaining coface

Native shifted-coface transposition, together with the exact original ordinal
casts, identifies each cone chart with the original remaining prefix coface.
No change of ambient simplex, replacement face or assumed cone isomorphism is
used. These equations verify the original maps of the inverse construction.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinalJoinLeft DaggerOriginalJoinedHornGeometry
open DaggerOriginalPrefixBoundaryConeOperators
open DaggerOriginalZeroJoinStandardCofaces DaggerOriginalZeroJoinStandardTransposition
open DaggerOriginalRestBoundaryInverseFaceMaps

namespace DaggerOriginalRestBoundaryConeFaceOperators

/-- The original standard coface and its original source/target casts commute exactly. -/
theorem coface_cast_inverse {m n : ℕ} (h : m = n) (i : Fin (n + 2)) :
    eqToHom (congrArg SimplexCategory.mk h) ≫ SimplexCategory.δ i ≫
        eqToHom (congrArg SimplexCategory.mk (congrArg (fun v ↦ v + 1) h).symm) =
      SimplexCategory.δ (Fin.cast (congrArg (fun v ↦ v + 2) h.symm) i) := by
  subst m
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Fin.cast_refl]
  rfl

/-- The native cone ambient cast is the exact inverse original successor face-target cast. -/
theorem zeroJoinStandardIso_inv_comp_ambient (k n : ℕ) :
    (zeroJoinStandardIso (k + n + 1)).inv ≫ (coneAmbientIso k n).hom =
      eqToHom (congrArg SimplexCategory.mk
        (congrArg (fun v ↦ v + 1) (restFaceDimension_eq k n)).symm) := by
  simp only [zeroJoinStandardIso, coneAmbientIso, eqToIso.inv, eqToIso.hom, eqToHom_trans]

/-- The actual inverse chart operator is the same original remaining-prefix coface. -/
theorem restConeFaceOperator_eq_coface (k n : ℕ) (j : Fin (k + 1)) :
    restFaceSourceCast k n ≫ (zeroJoinStandardIso (k + n)).inv ≫
        prefixConeOperator k n (SimplexCategory.δ (prefixIndex k n j)) =
      SimplexCategory.δ (prefixIndex (k + 1) n j.succ) := by
  dsimp only [prefixConeOperator]
  rw [← Category.assoc (zeroJoinStandardIso (k + n)).inv,
    zeroJoinStandardIso_inv_comp_coface]
  simp only [Category.assoc]
  rw [zeroJoinStandardIso_inv_comp_ambient]
  dsimp only [restFaceSourceCast]
  rw [coface_cast_inverse (restFaceDimension_eq k n) (prefixIndex k n j).succ,
    restFaceIndex_cast]

end DaggerOriginalRestBoundaryConeFaceOperators
