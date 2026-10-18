import NativeIhomProductSections
import NativeProductProjectionBaseChange

/-! Original maps over a product parameter act weakly on the exact internal-Hom section object. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite
open HomotopicalAlgebra Simplicial
open DaggerNativeIhomRelativeSectionsWeak DaggerNativeIhomProductSections
open DaggerNativeSimplexPullbackFibrationDetection
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeIhomProductSectionTransport
noncomputable section

theorem graph_app (K X : SSet.{u}) (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m)
    (f : ((ihom K).obj X).obj n) (k : K.obj m) :
    (((graph K X).app n f).app m i k) = (k, f.app m i k) := by
  apply Prod.ext
  · have h := congrArg (fun t : ((ihom K).obj K).obj n ↦ t.app m i k)
      (congrFun (NatTrans.congr_app (graph_fst K X) n) f)
    exact h
  · have h := congrArg (fun t : ((ihom K).obj X).obj n ↦ t.app m i k)
      (congrFun (NatTrans.congr_app (graph_snd K X) n) f)
    exact h

def sectionTransport {K X Y : SSet.{u}} (f : K ⊗ X ⟶ K ⊗ Y) :
    (ihom K).obj X ⟶ (ihom K).obj Y :=
  graph K X ≫ (ihom K).map f ≫ (ihom K).map (snd K Y)

theorem sectionTransport_app {K X Y : SSet.{u}} (f : K ⊗ X ⟶ K ⊗ Y)
    (n m : SimplexCategoryᵒᵖ) (i : n ⟶ m) (g : ((ihom K).obj X).obj n) (k : K.obj m) :
    ((sectionTransport f).app n g).app m i k = (f.app m (k, g.app m i k)).2 := by
  change (f.app m (((graph K X).app n g).app m i k)).2 = _
  rw [graph_app]

theorem sectionTransport_graph {K X Y : SSet.{u}} (f : K ⊗ X ⟶ K ⊗ Y)
    (h : f ≫ fst K Y = fst K X) :
    sectionTransport f ≫ graph K Y = graph K X ≫ (ihom K).map f := by
  apply (ihom_product_isPullback K Y).hom_ext
  · rw [Category.assoc, graph_snd, Category.comp_id]
    rfl
  · rw [Category.assoc, graph_fst, Category.assoc, ← Functor.map_comp, h, graph_fst]
    have ht : sectionTransport f ≫ toUnit ((ihom K).obj Y) = toUnit ((ihom K).obj X) :=
      isTerminalTensorUnit.hom_ext _ _
    rw [← Category.assoc, ht]

theorem productSectionIso_map {K X Y : SSet.{u}} (f : K ⊗ X ⟶ K ⊗ Y)
    (h : f ≫ fst K Y = fst K X) :
    (productSectionIso K X).hom ≫
      functionFibreMap K (fst K X) (fst K Y) f h (identityPoint K) =
        sectionTransport f ≫ (productSectionIso K Y).hom := by
  apply pullback.hom_ext
  · change _ ≫ pullback.fst ((ihom K).map (fst K Y)) (identityPoint K) = _
    dsimp only [functionFibreMap]
    rw [Category.assoc, DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst]
    change ((productSectionIso K X).hom ≫
      pullback.fst ((ihom K).map (fst K X)) (identityPoint K)) ≫ (ihom K).map f = _
    dsimp only [productSectionIso]
    rw [(graph_isPullback K X).isoPullback_hom_fst, Category.assoc,
      (graph_isPullback K Y).isoPullback_hom_fst]
    exact (sectionTransport_graph f h).symm
  · exact isTerminalTensorUnit.hom_ext _ _

theorem sectionTransport_weak {K X Y : SSet.{u}} (f : K ⊗ X ⟶ K ⊗ Y)
    (h : f ≫ fst K Y = fst K X) [X.KanComplex] [Y.KanComplex] [WeakEquivalence f] :
    WeakEquivalence (sectionTransport f) := by
  have : Fibration (fst K X) := product_projection_fibration _ _
  have : Fibration (fst K Y) := product_projection_fibration _ _
  have : WeakEquivalence (functionFibreMap K (fst K X) (fst K Y) f h (identityPoint K)) :=
    functionFibreMap_weak K (fst K X) (fst K Y) f h (identityPoint K)
  have hfac := productSectionIso_map f h
  have : WeakEquivalence ((productSectionIso K X).hom ≫
      functionFibreMap K (fst K X) (fst K Y) f h (identityPoint K)) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac hfac.symm

end
end DaggerNativeIhomProductSectionTransport
