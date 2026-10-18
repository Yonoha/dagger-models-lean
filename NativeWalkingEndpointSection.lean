import NativeWalkingMonoPushout
import NativeIhomQuasicategories

/-! The literal zero endpoint has a whole native internal-Hom section. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction
universe u v w
namespace DaggerNativeWalkingEndpointSection
noncomputable section

def projection : J.{u} ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from _

theorem zero_projection : zeroInclusion.{u} ≫ projection.{u} = 𝟙 (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

def endpointSection (Z : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj Z ⟶ (ihom J.{u}).obj Z :=
  (MonoidalClosed.pre projection.{u}).app Z

theorem endpointSection_comp (Z : SSet.{u}) :
    endpointSection Z ≫ (MonoidalClosed.pre zeroInclusion.{u}).app Z = 𝟙 _ := by
  unfold endpointSection
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, zero_projection,
    MonoidalClosed.pre_id, NatTrans.id_app]

theorem initial_section_lifting {C : Type w} [Category.{v} C] {A B X Y : C}
    (hA : IsInitial A) (i : A ⟶ B) (p : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    HasLiftingProperty i p := by
  constructor
  intro f g sq
  exact ⟨g ≫ s, hA.hom_ext _ _, by rw [Category.assoc, hs, Category.comp_id]⟩

theorem boundary_zero_lifting (Z : SSet.{u}) :
    HasLiftingProperty (SSet.boundary.{u} 0).ι
      ((MonoidalClosed.pre zeroInclusion.{u}).app Z) :=
  initial_section_lifting SSet.boundary.isInitial _ _ (endpointSection Z) (endpointSection_comp Z)

end
end DaggerNativeWalkingEndpointSection
