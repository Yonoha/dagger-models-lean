import DaggerModels.Presentable
import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Local finite presentability of the entire native simplicial-set category

Use the existing singleton strong generator of Type and Mathlib's free-Yoneda
strong generator, retaining the original simplex category in every universe.
-/
set_option autoImplicit false
open CategoryTheory Limits DaggerModels
universe u
namespace DaggerNativeSSetLocallyPresentable
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

instance locallyFinitelyPresentable : IsLocallyFinitelyPresentable.{u} SSet.{u} := by
  let P : ObjectProperty (Type u) := ObjectProperty.singleton PUnit
  let G := ObjectProperty.ofObj
    (fun T : SimplexCategory × Subtype P ↦ Presheaf.freeYoneda T.1 T.2.1)
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator.{u, u, u + 1}
    SSet.{u} Cardinal.aleph0.{u}).2
  refine ⟨G, inferInstance, Presheaf.isStrongGenerator (P := P) typeUnitStrongGenerator.{u}
    SimplexCategory, ?_⟩
  rintro _ ⟨⟨n, M, hM⟩⟩
  have hM' : IsCardinalPresentable M Cardinal.aleph0.{u} := by
    have hunit : IsCardinalPresentable (PUnit : Type u) Cardinal.aleph0.{u} :=
      HasCardinalLT.isCardinalPresentable
        (hasCardinalLT_of_finite PUnit Cardinal.aleph0.{u} le_rfl)
    have hEq : PUnit = M := (ObjectProperty.singleton_iff _ _).mp hM
    exact hEq ▸ hunit
  rw [isCardinalPresentable_iff]
  change IsCardinalPresentable (Presheaf.freeYoneda n M) Cardinal.aleph0.{u}
  infer_instance

instance locallyPresentable : IsLocallyPresentable.{u} SSet.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end
end DaggerNativeSSetLocallyPresentable
