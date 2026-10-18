import NativeSSetFibrationSquareFibreWeak
import NativeStandardSimplexContraction

/-! Native fibrations with weak actual vertex-fibre projections are trivial fibrations. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open DaggerNativeStandardSimplexContraction DaggerNativeSSetRawHomotopyEquivalenceWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFibrationWeakFromVertexFibres
noncomputable section

theorem first_vertex_weak (n : ℕ) :
    WeakEquivalence (SSet.const (firstVertex n) : (Δ[0] : SSet.{u}) ⟶ Δ[n]) := by
  let e : SSet.HomotopyEquiv (Δ[0] : SSet.{u}) Δ[n] :=
    { hom := SSet.const (firstVertex n)
      inv := SSet.stdSimplex.isTerminalObj₀.from _
      homInvId := by
        apply SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq
        congr 1
        exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      invHomId := (simplexContractible n).h.congr (by ext; rfl) rfl }
  exact rawHomotopyEquiv_weakEquivalence e

theorem simplex_pullback_weak {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hp : ∀ (b : (Δ[0] : SSet.{u}) ⟶ B), WeakEquivalence (pullback.snd p b))
    (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ B) :
    WeakEquivalence (pullback.snd p b) := by
  let v : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const (firstVertex n)
  let q := pullback.snd p b
  let t : pullback p (v ≫ b) ⟶ pullback p b :=
    pullback.lift (pullback.fst p (v ≫ b)) (pullback.snd p (v ≫ b) ≫ v)
      (by rw [Category.assoc, pullback.condition])
  have ht : t ≫ q = pullback.snd p (v ≫ b) ≫ v := by simp [t, q]
  have outer : IsPullback (t ≫ pullback.fst p b)
      (pullback.snd p (v ≫ b)) p (v ≫ b) := by
    simpa [t] using IsPullback.of_hasPullback p (v ≫ b)
  have sq : IsPullback t (pullback.snd p (v ≫ b)) q v :=
    outer.of_right ht (IsPullback.of_hasPullback p b)
  have : Fibration q := inferInstance
  have : WeakEquivalence v := first_vertex_weak n
  have : WeakEquivalence t := DaggerSSetRightProper.weakEquivalence_of_isPullback sq
  have : WeakEquivalence (pullback.snd p (v ≫ b)) := hp (v ≫ b)
  have : WeakEquivalence (pullback.snd p (v ≫ b) ≫ v) := inferInstance
  exact weakEquivalence_of_precomp_of_fac ht

theorem boundary_rlp_of_vertex_fibres_weak {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hp : ∀ (b : (Δ[0] : SSet.{u}) ⟶ B), WeakEquivalence (pullback.snd p b)) :
    SSet.modelCategoryQuillen.I.rlp p := by
  intro A K i hi
  obtain ⟨n⟩ := hi
  constructor
  intro a b sq
  have : Fibration (pullback.snd p b) := inferInstance
  have : WeakEquivalence (pullback.snd p b) := simplex_pullback_weak p hp n b
  have hq := (SSet.modelCategoryQuillen.weakEquivalence_iff_of_fibration
    (pullback.snd p b)).mpr inferInstance
  have := hq _ ⟨n⟩
  let t := pullback.lift a (SSet.boundary n).ι sq.w
  let sp : CommSq t (SSet.boundary n).ι (pullback.snd p b) (𝟙 _) := ⟨by simp [t]⟩
  refine ⟨sp.lift ≫ pullback.fst p b, ?_, ?_⟩
  · rw [← Category.assoc, sp.fac_left]
    simp [t]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, sp.fac_right, Category.id_comp]

theorem weak_of_vertex_fibres_weak {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (hp : ∀ (b : (Δ[0] : SSet.{u}) ⟶ B), WeakEquivalence (pullback.snd p b)) :
    WeakEquivalence p :=
  (SSet.modelCategoryQuillen.weakEquivalence_iff_of_fibration p).mp
    (boundary_rlp_of_vertex_fibres_weak p hp)

end
end DaggerNativeFibrationWeakFromVertexFibres
