import OriginalContinuousEndpointCylinderFamilies

/-!
# Naturality of the original realized singular cylinders

The existing realized one-simplex product isomorphism commutes with the actual original
parameter maps. Its two projections give the verification directly. The original singular
path hom equivalence consequently commutes with precomposition on the same parameters.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Opposite Simplicial
open DaggerOriginalSingularPathCylinderAdjunction DaggerOriginalSingularEndpointCylinderAdjunction

universe u

namespace DaggerOriginalSingularCylinderParameterNaturality

noncomputable section

/-- The first projection of the original realized cylinder is the realized original projection. -/
@[reassoc]
theorem realizedCylinder_hom_fst (A : SSet.{u}) :
    (SSet.stdSimplex.toTopTensorDeltaOneIso A).hom ≫ fst _ _ =
      SSet.toTop.map (fst A Δ[1]) := by
  simp [SSet.stdSimplex.toTopTensorDeltaOneIso]

/-- The second projection is the original realized interval projection with its native iso. -/
@[reassoc]
theorem realizedCylinder_hom_snd (A : SSet.{u}) :
    (SSet.stdSimplex.toTopTensorDeltaOneIso A).hom ≫ snd _ _ =
      SSet.toTop.map (snd A Δ[1]) ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
  simp [SSet.stdSimplex.toTopTensorDeltaOneIso]

/-- The original realized cylinder isomorphism commutes with the same parameter map. -/
theorem realizedCylinder_hom_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.toTop.map (f ▷ Δ[1]) ≫ (SSet.stdSimplex.toTopTensorDeltaOneIso B).hom =
      (SSet.stdSimplex.toTopTensorDeltaOneIso A).hom ≫ SSet.toTop.map f ▷ TopCat.I := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, realizedCylinder_hom_fst, whiskerRight_fst,
      realizedCylinder_hom_fst_assoc, ← Functor.map_comp]
  · simp only [Category.assoc, realizedCylinder_hom_snd, whiskerRight_snd]
    rw [← Functor.map_comp_assoc, whiskerRight_snd]

/-- The inverse cylinder isomorphism commutes with the same actual parameter map. -/
@[reassoc]
theorem realizedCylinder_inv_naturality {A B : SSet.{u}} (f : A ⟶ B) :
    SSet.toTop.map f ▷ TopCat.I ≫ (SSet.stdSimplex.toTopTensorDeltaOneIso B).inv =
      (SSet.stdSimplex.toTopTensorDeltaOneIso A).inv ≫ SSet.toTop.map (f ▷ Δ[1]) := by
  rw [← cancel_mono (SSet.stdSimplex.toTopTensorDeltaOneIso B).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    realizedCylinder_hom_naturality, Iso.inv_hom_id_assoc]

/-- Original path currying commutes with precomposition by the actual original parameter map. -/
theorem singularPathHomCylinderEquiv_parameter_naturality (T : TopCat.{u})
    {A B : SSet.{u}} (f : A ⟶ B) (q : B ⟶ (TopCat.toSSet.obj T).path) :
    singularPathHomCylinderEquiv T A (f ≫ q) =
      SSet.toTop.map f ▷ TopCat.I ≫ singularPathHomCylinderEquiv T B q := by
  rw [singularPathHomCylinderEquiv_apply, singularPathHomCylinderEquiv_apply,
    realizedCylinder_inv_naturality_assoc,
    ← sSetTopAdj.homEquiv_naturality_left_symm]
  congr 2

end

end DaggerOriginalSingularCylinderParameterNaturality
