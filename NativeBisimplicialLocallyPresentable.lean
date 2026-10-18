import NativeSSetLocallyPresentable
import NativeBisimplicialHorizontalMapping
import Mathlib.CategoryTheory.Presentable.Presheaf

/-! Native strong generators for the original bisimplicial category in every universe. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeBisimplicialHorizontalMapping
universe u
namespace DaggerNativeBisimplicialLocallyPresentable
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

instance locallyFinitelyPresentable : IsLocallyFinitelyPresentable.{u} BiSSet.{u} := by
  obtain ⟨P, hsmall, hstrong, hp⟩ :=
    (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
      SSet.{u} Cardinal.aleph0.{u}).mp inferInstance
  let G := ObjectProperty.ofObj
    (fun T : SimplexCategory × Subtype P ↦ Presheaf.freeYoneda T.1 T.2.1)
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    BiSSet.{u} Cardinal.aleph0.{u}).mpr
  refine ⟨G, inferInstance, Presheaf.isStrongGenerator hstrong SimplexCategory, ?_⟩
  rintro _ ⟨⟨n, M, hM⟩⟩
  have hM' : IsCardinalPresentable M Cardinal.aleph0.{u} := by
    rw [← isCardinalPresentable_iff]
    exact hp M hM
  rw [isCardinalPresentable_iff]
  change IsCardinalPresentable (Presheaf.freeYoneda n M) Cardinal.aleph0.{u}
  infer_instance

instance locallyPresentable : IsLocallyPresentable.{u} BiSSet.{u} where
  exists_cardinal := ⟨Cardinal.aleph0.{u}, inferInstance, inferInstance⟩

end
end DaggerNativeBisimplicialLocallyPresentable
