import NativeFibrationWeakFromVertexFibres

/-! Vertexwise recognition of weak maps between actual fibrations over the same base. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open DaggerNativeFibrationWeakFromVertexFibres
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFibrewiseWeakRecognition
noncomputable section

theorem fibration_weak_of_vertex_base_changes {X Y B : SSet.{u}}
    (q : Y ⟶ B) (f : X ⟶ Y) [Fibration f]
    (hf : ∀ (b : (Δ[0] : SSet.{u}) ⟶ B),
      WeakEquivalence (mapOver (f ≫ q) q f rfl b)) : WeakEquivalence f := by
  apply weak_of_vertex_fibres_weak f
  intro y
  let b := y ≫ q
  let fy := mapOver (f ≫ q) q f rfl b
  let s : (Δ[0] : SSet.{u}) ⟶ pullback q b :=
    pullback.lift y (𝟙 _) (by simp [b])
  let t : pullback f y ⟶ pullback (f ≫ q) b :=
    pullback.lift (pullback.fst f y) (pullback.snd f y) (by
      rw [← Category.assoc, pullback.condition, Category.assoc])
  have ht : t ≫ fy = pullback.snd f y ≫ s := by
    apply pullback.hom_ext <;> simp [t, fy, s, mapOver, pullback.condition]
  have outer : IsPullback (t ≫ pullback.fst (f ≫ q) b)
      (pullback.snd f y) f (s ≫ pullback.fst q b) := by
    simpa [t, s] using IsPullback.of_hasPullback f y
  have sq : IsPullback t (pullback.snd f y) fy s :=
    outer.of_right ht (mapOver_isPullback (f ≫ q) q f rfl b).flip
  have : Fibration fy := (HomotopicalAlgebra.fibration_iff fy).mpr
    (MorphismProperty.of_isPullback (P := fibrations SSet)
      (mapOver_isPullback (f ≫ q) q f rfl b).flip
      ((HomotopicalAlgebra.fibration_iff f).mp inferInstance))
  have : WeakEquivalence fy := hf b
  exact (mem_trivialFibrations_iff (pullback.snd f y)).mp
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
      ((mem_trivialFibrations_iff fy).mpr ⟨inferInstance, inferInstance⟩)) |>.2

theorem weak_of_vertex_base_changes {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ q = p) [Fibration p] [Fibration q]
    (hf : ∀ (b : (Δ[0] : SSet.{u}) ⟶ B), WeakEquivalence (mapOver p q f h b)) :
    WeakEquivalence f := by
  let d := MorphismProperty.factorizationData (trivialCofibrations SSet)
    (fibrations SSet) f
  have : WeakEquivalence d.i := (mem_trivialCofibrations_iff d.i).mp d.hi |>.2
  have : Fibration d.p := (HomotopicalAlgebra.fibration_iff d.p).mpr d.hp
  let r := d.p ≫ q
  have : Fibration r := inferInstance
  have hi : d.i ≫ r = p := by rw [← Category.assoc, d.fac, h]
  have : WeakEquivalence d.p := by
    apply fibration_weak_of_vertex_base_changes q d.p
    intro b
    let a := mapOver p r d.i hi b
    have : WeakEquivalence a := mapOver_weakEquivalence p r d.i hi b
    have fac : a ≫ mapOver r q d.p rfl b = mapOver p q f h b := by
      apply pullback.hom_ext <;> simp [a, mapOver, d.fac]
    have : WeakEquivalence (mapOver p q f h b) := hf b
    exact weakEquivalence_of_precomp_of_fac fac
  rw [← d.fac]
  infer_instance

theorem weak_iff_vertex_base_changes {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (f : X ⟶ Y) (h : f ≫ q = p) [Fibration p] [Fibration q] :
    WeakEquivalence f ↔ ∀ (b : (Δ[0] : SSet.{u}) ⟶ B),
      WeakEquivalence (mapOver p q f h b) := by
  constructor
  · intro hf b
    have := hf
    exact mapOver_weakEquivalence p q f h b
  · exact weak_of_vertex_base_changes p q f h

end
end DaggerNativeFibrewiseWeakRecognition
