import NativeFullGroupoidNerveFibration
import NativeOverGroupoidNerveKan

/-! Over-category nerves inherit Kan fibrations from strict object-surjective evaluations. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeOverGroupoidNerveKan DaggerNativeFullGroupoidNerveFibration
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGroupoidOverEvaluationFibration
noncomputable section

instance over_post_full {C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (F : C ⥤ D) (z : C) : (Over.post F : Over z ⥤ Over (F.obj z)).Full :=
  ⟨fun {X Y} f ↦ ⟨overHom C z X Y, overHom_unique D (F.obj z) _ f⟩⟩

theorem over_nerve_fibration {C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (F : C ⥤ D) (z : C)
    (hF : Function.Surjective (Over.post F : Over z ⥤ Over (F.obj z)).obj) :
    Fibration (nerveMap (Over.post F : Over z ⥤ Over (F.obj z))) := by
  letI : Groupoid.{u} (Over z) := overGroupoid C z
  letI : Groupoid.{u} (Over (F.obj z)) := overGroupoid D (F.obj z)
  exact full_nerve_fibration (Over.post F : Over z ⥤ Over (F.obj z)) hF

theorem over_nerve_fibration_of_groupoid_categories {C D : Type u}
    [cC : Category.{u} C] [cD : Category.{u} D]
    (hC : ∃ G : Groupoid.{u} C, G.toCategory = cC)
    (hD : ∃ G : Groupoid.{u} D, G.toCategory = cD)
    (F : C ⥤ D) (z : C)
    (hF : Function.Surjective (Over.post F : Over z ⥤ Over (F.obj z)).obj) :
    Fibration (nerveMap (Over.post F : Over z ⥤ Over (F.obj z))) := by
  obtain ⟨G, hG⟩ := hC
  obtain ⟨H, hH⟩ := hD
  cases hG
  cases hH
  letI : Groupoid.{u} C := G
  letI : Groupoid.{u} D := H
  exact over_nerve_fibration F z hF

end
end DaggerNativeGroupoidOverEvaluationFibration
