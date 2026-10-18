import OriginalSimplicialCategoryBarRowPullbackTransport

/-! Native Kan fibrations are detected by all actual pullbacks over standard simplices. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial MonoidalCategory
open CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplexPullbackFibrationDetection
noncomputable section

theorem fibration_of_simplex_pullbacks {E B : SSet.{u}} (p : E ⟶ B)
    (hp : ∀ (n : ℕ) (b : (Δ[n] : SSet.{u}) ⟶ B), Fibration (pullback.snd p b)) :
    Fibration p := by
  apply (SSet.modelCategoryQuillen.fibration_iff p).mpr
  intro A K i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  constructor
  intro a b sq
  have := hp (n + 1) b
  let t := pullback.lift a (SSet.horn (n + 1) k).ι sq.w
  let sp : CommSq t (SSet.horn (n + 1) k).ι (pullback.snd p b) (𝟙 _) :=
    ⟨by simp [t]⟩
  refine ⟨sp.lift ≫ pullback.fst p b, ?_, ?_⟩
  · rw [← Category.assoc, sp.fac_left]
    simp [t]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, sp.fac_right, Category.id_comp]

theorem product_projection_fibration (K L : SSet.{u}) [L.KanComplex] :
    Fibration (fst K L) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  constructor
  intro a b sq
  obtain ⟨l, hl⟩ := SSet.KanComplex.hornFilling (a ≫ snd K L)
  refine ⟨lift b l, ?_, ?_⟩
  · apply NatTrans.ext
    funext q x
    exact Prod.ext (congrFun (NatTrans.congr_app sq.w.symm q) x)
      (congrFun (NatTrans.congr_app hl.symm q) x)
  · apply NatTrans.ext
    rfl

end
end DaggerNativeSimplexPullbackFibrationDetection
