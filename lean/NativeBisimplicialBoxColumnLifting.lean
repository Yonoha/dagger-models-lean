import NativeBisimplicialBoxHorizontalHom
import NativeBisimplicialRelativeLifting

/-! Original column fibrations lift the second box factor with the original horn inclusion. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxHom DaggerNativeBisimplicialHorizontalTranspose
open DaggerNativeBisimplicialBoxHorizontalHom DaggerNativeBisimplicialRelativeLifting
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBisimplicialBoxColumnLifting
noncomputable section

theorem horizontalCurry_post (K B : SSet.{u}) {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (g : box K B ⟶ X) :
    horizontalCurry K B Y (g ≫ f) =
      horizontalCurry K B X g ≫ horizontalMap B (flipMap f) := by
  change transpose K B Y (boxCurry K B Y (g ≫ f)) = _
  rw [boxCurry_post, transpose_post]
  rfl

theorem box_horizontal_lifting {K L B : SSet.{u}} (i : K ⟶ L)
    {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hf : HasLiftingProperty i (horizontalMap B (flipMap f))) :
    HasLiftingProperty (boxMap i (𝟙 B)) f := by
  constructor
  intro a b sq
  have he := congrArg (horizontalCurry K B Y) sq.w
  rw [horizontalCurry_post, horizontalCurry_pre] at he
  have ss : CommSq (horizontalCurry K B X a) i (horizontalMap B (flipMap f))
      (horizontalCurry L B Y b) := ⟨he⟩
  have : HasLiftingProperty i (horizontalMap B (flipMap f)) := hf
  refine ⟨horizontalUncurry L B X ss.lift, ?_, ?_⟩
  · apply (horizontalBoxEquiv K B X).injective
    change horizontalCurry K B X (boxMap i (𝟙 B) ≫ horizontalUncurry L B X ss.lift) = _
    rw [horizontalCurry_pre]
    change i ≫ (horizontalBoxEquiv L B X)
      ((horizontalBoxEquiv L B X).symm ss.lift) = _
    rw [Equiv.apply_symm_apply]
    exact ss.fac_left
  · apply (horizontalBoxEquiv L B Y).injective
    change horizontalCurry L B Y (horizontalUncurry L B X ss.lift ≫ f) = _
    rw [horizontalCurry_post]
    change (horizontalBoxEquiv L B X) ((horizontalBoxEquiv L B X).symm ss.lift) ≫
      horizontalMap B (flipMap f) = _
    rw [Equiv.apply_symm_apply]
    exact ss.fac_right

def columnMappingArrowIso {X Y : BiSSet.{u}} (f : X ⟶ Y) (r : ℕ) :
    Arrow.mk (horizontalMap (Δ[r] : SSet.{u}) (flipMap f)) ≅
      Arrow.mk ((flipMap f).app (op ⦋r⦌)) :=
  Arrow.isoMk (horizontalSimplexIso X.flip r) (horizontalSimplexIso Y.flip r)
    (horizontalSimplexIso_natural (flipMap f) r)

theorem column_mapping_fibration {X Y : BiSSet.{u}} (f : X ⟶ Y) (r : ℕ)
    [Fibration (C := SSet.{u}) ((flipMap f).app (op ⦋r⦌))] :
    Fibration (horizontalMap (Δ[r] : SSet.{u}) (flipMap f)) := by
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff (columnMappingArrowIso f r)).mpr
      ((fibration_iff (C := SSet.{u}) _).mp inferInstance))

theorem box_horn_lifting {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (hc : ∀ v : SimplexCategoryᵒᵖ, Fibration (C := SSet.{u}) ((flipMap f).app v))
    (m : ℕ) (k : Fin (m + 2)) (r : ℕ) :
    HasLiftingProperty (boxMap (SSet.horn (m + 1) k).ι (𝟙 (Δ[r] : SSet.{u}))) f := by
  have : Fibration (C := SSet.{u}) ((flipMap f).app (op ⦋r⦌)) := hc _
  have hq := column_mapping_fibration f r
  apply box_horizontal_lifting _ f
  apply (SSet.modelCategoryQuillen.fibration_iff _).mp hq
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff]
  exact ⟨m, ⟨k⟩⟩

end
end DaggerNativeBisimplicialBoxColumnLifting
