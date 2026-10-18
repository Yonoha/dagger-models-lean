import NativeBisimplicialBoxHom
import NativeBisimplicialReedyRestrictions

/-! Genuine Reedy fibrations extend the original compatible pair of box boundary maps. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxHom DaggerNativeBisimplicialReedyRestrictions
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyBoxExtension
noncomputable section

theorem compatible_box_extension {K L A B : SSet.{u}} (i : K ⟶ L) (j : A ⟶ B)
    [Mono i] [Cofibration j] [WeakEquivalence j]
    {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f)
    (a : box L A ⟶ X) (b : box K B ⟶ X) (c : box L B ⟶ Y)
    (hab : boxMap i (𝟙 A) ≫ a = boxMap (𝟙 K) j ≫ b)
    (hac : a ≫ f = boxMap (𝟙 L) j ≫ c)
    (hbc : b ≫ f = boxMap i (𝟙 B) ≫ c) :
    ∃ d : box L B ⟶ X, boxMap (𝟙 L) j ≫ d = a ∧
      boxMap i (𝟙 B) ≫ d = b ∧ d ≫ f = c := by
  have hh := congrArg (boxCurry K B Y) hbc
  rw [boxCurry_post, boxCurry_pre, Category.id_comp] at hh
  let z := pullback.lift (boxCurry K B X b) (boxCurry L B Y c) hh
  have sq : CommSq (boxCurry L A X a) j (relativeRestriction i f) z := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeRestriction_fst, z, pullback.lift_fst]
      have he := congrArg (boxCurry K A X) hab
      rw [boxCurry_pre, boxCurry_pre] at he
      simpa only [Category.id_comp, horizontalPre_id, Category.comp_id] using he
    · simp only [Category.assoc, relativeRestriction_snd, z, pullback.lift_snd]
      have he := congrArg (boxCurry L A Y) hac
      rw [boxCurry_post, boxCurry_pre] at he
      simpa only [horizontalPre_id, Category.comp_id] using he
  have : Fibration (relativeRestriction i f) := restriction_fibration f hf i
  have : HasLiftingProperty j (relativeRestriction i f) := inferInstance
  refine ⟨boxUncurry L B X sq.lift, ?_, ?_, ?_⟩
  · apply (boxHomEquiv L A X).injective
    change boxCurry L A X (boxMap (𝟙 L) j ≫ boxUncurry L B X sq.lift) = boxCurry L A X a
    rw [boxCurry_pre, horizontalPre_id, Category.comp_id]
    change j ≫ (boxHomEquiv L B X) ((boxHomEquiv L B X).symm sq.lift) = _
    rw [Equiv.apply_symm_apply]
    exact sq.fac_left
  · apply (boxHomEquiv K B X).injective
    change boxCurry K B X (boxMap i (𝟙 B) ≫ boxUncurry L B X sq.lift) = boxCurry K B X b
    rw [boxCurry_pre, Category.id_comp]
    change (boxHomEquiv L B X) ((boxHomEquiv L B X).symm sq.lift) ≫ horizontalPre i X = _
    rw [Equiv.apply_symm_apply]
    have he := congrArg
      (fun t ↦ t ≫ pullback.fst (horizontalMap K f) (horizontalPre i Y)) sq.fac_right
    simpa only [Category.assoc, relativeRestriction_fst, z, pullback.lift_fst] using he
  · apply (boxHomEquiv L B Y).injective
    change boxCurry L B Y (boxUncurry L B X sq.lift ≫ f) = boxCurry L B Y c
    rw [boxCurry_post]
    change (boxHomEquiv L B X) ((boxHomEquiv L B X).symm sq.lift) ≫ horizontalMap L f = _
    rw [Equiv.apply_symm_apply]
    have he := congrArg
      (fun t ↦ t ≫ pullback.snd (horizontalMap K f) (horizontalPre i Y)) sq.fac_right
    simpa only [Category.assoc, relativeRestriction_snd, z, pullback.lift_snd] using he

end
end DaggerNativeReedyBoxExtension
