import OriginalStrictGroupoidHomFaceCorrection

/-!
# Preserve the already corrected original faces

Instantiate the general correction square with Mathlib's literal simplicial identities.
The lower correction preserves earlier compatible faces. The upper correction preserves
both earlier compatible faces and later compatible faces. All equations concern the
unchanged original enriched mapping simplicial set and its actual groupoid operations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictSimplicialGroupoidHomOperations
open DaggerOriginalStrictGroupoidHomFaceCorrection

universe u

namespace DaggerOriginalStrictGroupoidHomFacePreservation

noncomputable section

/-- A lower correction keeps each earlier original face under the original matching equation.
-/
theorem lowerCorrection_preserves_lower (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 2)) (hk : k ≤ j.castSucc)
    {x y : C.Obj} (w : PointHom C (n + 2) x y) (a : PointHom C (n + 1) x y)
    (hmatch : (C.enriched.Hom x y).δ k a =
      (C.enriched.Hom x y).δ j.castSucc ((C.enriched.Hom x y).δ k.castSucc w)) :
    (C.enriched.Hom x y).δ k.castSucc (lowerCorrection C hC (n + 1) j.succ w a) =
      (C.enriched.Hom x y).δ k.castSucc w := by
  refine correctedHom_preserves C hC (SimplexCategory.σ j.succ).op
    (SimplexCategory.δ j.succ.castSucc).op (SimplexCategory.δ k.castSucc).op
    (SimplexCategory.δ k).op (SimplexCategory.σ j).op ?_ w a ?_
  · simp only [← op_comp, SimplexCategory.δ_comp_σ_of_le hk]
  · change (C.enriched.Hom x y).δ k a =
      (C.enriched.Hom x y).δ k ((C.enriched.Hom x y).δ j.castSucc.succ w)
    rw [SSet.δ_comp_δ_apply hk]
    exact hmatch

/-- An upper correction keeps each earlier original face under the original matching equation.
-/
theorem upperCorrection_preserves_lower (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 2)) (hk : k ≤ j.castSucc)
    {x y : C.Obj} (w : PointHom C (n + 2) x y) (a : PointHom C (n + 1) x y)
    (hmatch : (C.enriched.Hom x y).δ k a =
      (C.enriched.Hom x y).δ j.succ ((C.enriched.Hom x y).δ k.castSucc w)) :
    (C.enriched.Hom x y).δ k.castSucc (upperCorrection C hC (n + 1) j.succ w a) =
      (C.enriched.Hom x y).δ k.castSucc w := by
  refine correctedHom_preserves C hC (SimplexCategory.σ j.succ).op
    (SimplexCategory.δ j.succ.succ).op (SimplexCategory.δ k.castSucc).op
    (SimplexCategory.δ k).op (SimplexCategory.σ j).op ?_ w a ?_
  · simp only [← op_comp, SimplexCategory.δ_comp_σ_of_le hk]
  · have hk' : k ≤ j.succ := by
      change k.val ≤ j.val + 1
      have h := Fin.le_def.mp hk
      simp only [Fin.val_castSucc] at h
      omega
    change (C.enriched.Hom x y).δ k a =
      (C.enriched.Hom x y).δ k ((C.enriched.Hom x y).δ j.succ.succ w)
    rw [SSet.δ_comp_δ_apply hk']
    exact hmatch

/-- An upper correction keeps each later original face under the original matching equation.
-/
theorem upperCorrection_preserves_upper (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (n : ℕ) (j : Fin (n + 1)) (k : Fin (n + 2)) (hk : j.castSucc < k)
    {x y : C.Obj} (w : PointHom C (n + 2) x y) (a : PointHom C (n + 1) x y)
    (hmatch : (C.enriched.Hom x y).δ k a =
      (C.enriched.Hom x y).δ j.succ ((C.enriched.Hom x y).δ k.succ w)) :
    (C.enriched.Hom x y).δ k.succ (upperCorrection C hC (n + 1) j.castSucc w a) =
      (C.enriched.Hom x y).δ k.succ w := by
  refine correctedHom_preserves C hC (SimplexCategory.σ j.castSucc).op
    (SimplexCategory.δ j.castSucc.succ).op (SimplexCategory.δ k.succ).op
    (SimplexCategory.δ k).op (SimplexCategory.σ j).op ?_ w a ?_
  · simp only [← op_comp, SimplexCategory.δ_comp_σ_of_gt hk]
  · have hk' : j.succ ≤ k := by
      change j.val + 1 ≤ k.val
      have h := Fin.lt_def.mp hk
      simp only [Fin.val_castSucc] at h
      omega
    change (C.enriched.Hom x y).δ k a =
      (C.enriched.Hom x y).δ k ((C.enriched.Hom x y).δ j.succ.castSucc w)
    rw [← SSet.δ_comp_δ_apply hk']
    exact hmatch

end

end DaggerOriginalStrictGroupoidHomFacePreservation
