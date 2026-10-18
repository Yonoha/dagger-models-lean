import NativeSSetFibrationsOverBaseWeakPullbacks
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! Exact internal-Hom fibres preserve weak maps between fibrations over the original base. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeIhomRelativeSectionsWeak
noncomputable section

theorem left_tensor_mono (K : SSet.{u}) {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Mono (K ◁ i) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro n
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  change (x.1, i.app n x.2) = (y.1, i.app n y.2) at h
  exact Prod.ext (congrArg (fun p : K.obj n × B.obj n ↦ p.1) h)
    ((CategoryTheory.mono_iff_injective (i.app n)).mp inferInstance
      (congrArg (fun p : K.obj n × B.obj n ↦ p.2) h))

theorem ihom_trivialFibration (K : SSet.{u}) {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] : trivialFibrations SSet.{u} ((ihom K).map p) := by
  rw [← cofibrations_rlp]
  intro A B i hi
  have : Cofibration i := (HomotopicalAlgebra.cofibration_iff i).mpr hi
  have : Mono i := (SSet.modelCategoryQuillen.cofibration_iff i).mp inferInstance
  have : Mono (K ◁ i) := left_tensor_mono K i
  have : Cofibration (K ◁ i) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  have hp : (cofibrations SSet.{u}).rlp p := by
    rw [cofibrations_rlp]
    exact (mem_trivialFibrations_iff p).mpr ⟨inferInstance, inferInstance⟩
  exact ((ihom.adjunction K).hasLiftingProperty_iff i p).mp
    (hp (K ◁ i) ((HomotopicalAlgebra.cofibration_iff (K ◁ i)).mp inferInstance))

def functionFibreMap (K : SSet.{u}) {X Y B V : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ q = p) (b : V ⟶ (ihom K).obj B) :
    pullback ((ihom K).map p) b ⟶ pullback ((ihom K).map q) b :=
  mapOver ((ihom K).map p) ((ihom K).map q) ((ihom K).map f)
    (by rw [← Functor.map_comp, h]) b

theorem functionFibreMap_trivialFibration (K : SSet.{u}) {X Y B V : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (h : f ≫ q = p)
    (b : V ⟶ (ihom K).obj B) [Fibration f] [WeakEquivalence f] :
    trivialFibrations SSet.{u} (functionFibreMap K p q f h b) := by
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (mapOver_isPullback ((ihom K).map p) ((ihom K).map q) ((ihom K).map f)
      (by rw [← Functor.map_comp, h]) b).flip (ihom_trivialFibration K f)

theorem functionFibreMap_weak (K : SSet.{u}) {X Y B V : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ B) (f : X ⟶ Y) (h : f ≫ q = p)
    (b : V ⟶ (ihom K).obj B) [Fibration p] [Fibration q] [WeakEquivalence f] :
    WeakEquivalence (functionFibreMap K p q f h b) := by
  obtain ⟨Z, i, r, s, hi, hr, hwr, hs, hws, hir, his, hrs⟩ := relativeBrown p q f h
  have := hr
  have := hwr
  have := hs
  have := hws
  let z := r ≫ p
  let rK := functionFibreMap K z p r rfl b
  let sK := functionFibreMap K z q s hrs.symm b
  have hrK : WeakEquivalence rK :=
    (mem_trivialFibrations_iff _).mp (functionFibreMap_trivialFibration K z p r rfl b) |>.2
  have hsK : WeakEquivalence sK :=
    (mem_trivialFibrations_iff _).mp (functionFibreMap_trivialFibration K z q s hrs.symm b) |>.2
  have hiz : i ≫ z = p := by dsimp only [z]; rw [← Category.assoc, hir, Category.id_comp]
  let iK := functionFibreMap K p z i hiz b
  have hirK : iK ≫ rK = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [iK, rK, functionFibreMap, mapOver,
      ← Functor.map_comp, hir]
  have hisK : iK ≫ sK = functionFibreMap K p q f h b := by
    apply pullback.hom_ext <;> simp [iK, sK, functionFibreMap, mapOver,
      ← Functor.map_comp, his]
  have : WeakEquivalence iK := weakEquivalence_of_postcomp_of_fac hirK
  rw [← hisK]
  infer_instance

end
end DaggerNativeIhomRelativeSectionsWeak
