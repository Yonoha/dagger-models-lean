import NativeRealEdgewiseExactness
import ActualQWeightedAugmentationFilteredColimits
import ActualQWeightedAugmentationCoproducts

/-! Apply existing geometric gluing and colimit theorems to the literal edgewise target map. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerNativeRealEdgewiseSSet DaggerNativeRealEdgewiseExactness
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealEdgewiseTargetClosure
noncomputable section

private abbrev F : SSet.{u} ⥤ SSet.{u} := edgewise
private abbrev G : SSet.{u} ⥤ SSet.{u} := 𝟭 SSet.{u}

theorem pushout_GW {A X Z P : SSet.{u}} (k : A ⟶ X) (ell : A ⟶ Z)
    (r : X ⟶ P) (s : Z ⟶ P) (sq : IsPushout k ell r s) [Mono k]
    (hA : GW (targetNatural.app A)) (hX : GW (targetNatural.app X))
    (hZ : GW (targetNatural.app Z)) : GW (targetNatural.app P) := by
  have : Mono (F.map k) := inferInstance
  have : Mono (G.map k) := inferInstance
  exact geometric_of_pushout_cube
    (F.map k) (F.map ell) (F.map r) (F.map s)
    (G.map k) (G.map ell) (G.map r) (G.map s)
    (sq.map F) (sq.map G)
    (targetNatural.app A) (targetNatural.app X) (targetNatural.app Z) (targetNatural.app P)
    (targetNatural.naturality k) (targetNatural.naturality ell)
    (targetNatural.naturality r) (targetNatural.naturality s) hA hX hZ

theorem coproduct_square {J : Type u} (X : J → SSet.{u}) :
    sigmaComparison F X ≫ targetNatural.app (∐ X) =
      Limits.Sigma.map (fun j ↦ targetNatural.app (X j)) ≫ sigmaComparison G X := by
  apply Limits.Sigma.hom_ext
  intro j
  simp only [ι_comp_sigmaComparison_assoc, Limits.Sigma.ι_map_assoc,
    ι_comp_sigmaComparison]
  exact targetNatural.naturality (Limits.Sigma.ι X j)

theorem coproduct_GW {J : Type u} (X : J → SSet.{u})
    (hX : ∀ j, GW (targetNatural.app (X j))) : GW (targetNatural.app (∐ X)) := by
  have : WeakEquivalence (Limits.Sigma.map (fun j ↦ targetNatural.app (X j))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerOriginalFlagFlankification.sigmaMap_GW _ hX)
  have : WeakEquivalence (sigmaComparison F X) := inferInstance
  have : WeakEquivalence (sigmaComparison G X) := inferInstance
  exact (weakEquivalence_iff_GW _).mp
    (weakEquivalence_of_precomp_of_fac (coproduct_square X))

theorem sequential_GW (D : ℕ ⥤ SSet.{u}) (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ {a b : ℕ} (f : a ⟶ b), Mono (D.map f))
    (hη : ∀ n, GW (targetNatural.app (D.obj n))) : GW (targetNatural.app c.pt) := by
  apply DaggerGeometricFilteredColimits.geometric_of_nat_mono
    (isColimitOfPreserves F hc) (isColimitOfPreserves G hc)
    (fun {a b} f ↦ ?_) (fun {a b} f ↦ ?_)
    (D.whiskerLeft targetNatural) (targetNatural.app c.pt)
    (fun j ↦ targetNatural.naturality (c.ι.app j)) hη
  · have : Mono (D.map f) := hD f
    change Mono (F.map (D.map f))
    infer_instance
  · have : Mono (D.map f) := hD f
    change Mono (G.map (D.map f))
    infer_instance

theorem iso_GW {X Y : SSet.{u}} (e : X ≅ Y)
    (hX : GW (targetNatural.app X)) : GW (targetNatural.app Y) := by
  have : WeakEquivalence (targetNatural.app X) := (weakEquivalence_iff_GW _).mpr hX
  have : WeakEquivalence (F.map e.hom) := inferInstance
  have : WeakEquivalence (G.map e.hom) := inferInstance
  exact (weakEquivalence_iff_GW _).mp
    (weakEquivalence_of_precomp_of_fac (targetNatural.naturality e.hom))

theorem initial_GW (X : SSet.{u}) (hX : IsInitial X) : GW (targetNatural.app X) := by
  have hF : IsInitial (F.obj X) := initialIsInitial.ofIso
    ((PreservesInitial.iso F.{u}).symm ≪≫ F.mapIso (initialIsoIsInitial hX))
  have hG : IsInitial (G.obj X) := initialIsInitial.ofIso
    ((PreservesInitial.iso G.{u}).symm ≪≫ G.mapIso (initialIsoIsInitial hX))
  have : IsIso (targetNatural.app X) := isIso_of_isInitial hF hG _
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerNativeRealEdgewiseTargetClosure
