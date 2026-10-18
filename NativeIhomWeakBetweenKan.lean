import NativeIhomRelativeSectionsWeak

/-! Relative Brown preserves weak maps between Kan targets under native internal Hom. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open HomotopicalAlgebra
open DaggerNativeIhomRelativeSectionsWeak DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeIhomWeakBetweenKan
noncomputable section

theorem ihom_map_weak (K : SSet.{u}) {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence ((ihom K).map f) := by
  let T := 𝟙_ SSet.{u}
  let hT : IsTerminal T := isTerminalTensorUnit
  let hKT : IsTerminal ((ihom K).obj T) := IsTerminal.isTerminalObj (ihom K) T hT
  let e := hT.uniqueUpToIso hKT
  let p : X ⟶ T := toUnit X
  let q : Y ⟶ T := toUnit Y
  have h : f ≫ q = p := hT.hom_ext _ _
  have : Fibration p := (isFibrant_iff_of_isTerminal p hT).1 inferInstance
  have : Fibration q := (isFibrant_iff_of_isTerminal q hT).1 inferInstance
  let g := functionFibreMap K p q f h e.hom
  have : WeakEquivalence g := functionFibreMap_weak K p q f h e.hom
  have hp : WeakEquivalence (pullback.fst ((ihom K).map p) e.hom) := inferInstance
  have hq : WeakEquivalence (pullback.fst ((ihom K).map q) e.hom) := inferInstance
  have w : pullback.fst ((ihom K).map p) e.hom ≫ (ihom K).map f =
      g ≫ pullback.fst ((ihom K).map q) e.hom := by
    simp only [g, functionFibreMap, mapOver, pullback.lift_fst]
  have : WeakEquivalence (g ≫ pullback.fst ((ihom K).map q) e.hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac w

end
end DaggerNativeIhomWeakBetweenKan
