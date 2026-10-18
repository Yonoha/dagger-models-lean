import NativeDiagonalHornSkeletonData
import NativeBisimplicialBoxHorizontalHom

/-! Glue all chosen cell boxes through the existing native skeleton pushout. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxHorizontalHom DaggerNativeDiagonalHornSkeletonData
universe u
namespace DaggerNativeDiagonalHornSkeletonGluing
noncomputable section

theorem glue_successor {n : ℕ} (k : Fin (n + 1)) (d : ℕ) (X : BiSSet.{u})
    (g : box (stage k d : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X)
    (z : Cell k d → (box (Δ[d] : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X))
    (hz : ∀ s, boxMap (SSet.boundary d).ι (𝟙 (Δ[n] : SSet.{u})) ≫ z s =
      boxMap (oldFace k d s) (𝟙 (Δ[n] : SSet.{u})) ≫ g) :
    ∃ g' : box (stage k (d + 1) : SSet.{u}) (Δ[n] : SSet.{u}) ⟶ X,
      boxMap (step k d) (𝟙 (Δ[n] : SSet.{u})) ≫ g' = g ∧
      ∀ s, boxMap (newFace k d s) (𝟙 (Δ[n] : SSet.{u})) ≫ g' = z s := by
  let c₁ := horizontalCurry (stage k d : SSet.{u}) (Δ[n] : SSet.{u}) X g
  let c₂ := Sigma.desc (fun s ↦ horizontalCurry (Δ[d] : SSet.{u}) (Δ[n] : SSet.{u}) X (z s))
  have he : SSet.relativeCellComplexOfMono.t (base k) d ≫ c₁ =
      SSet.relativeCellComplexOfMono.m (base k) d ≫ c₂ := by
    apply Sigma.hom_ext
    intro s
    change SSet.relativeCellComplexOfMono.ιA s ≫
        SSet.relativeCellComplexOfMono.t (base k) d ≫ c₁ =
      SSet.relativeCellComplexOfMono.ιA s ≫
        SSet.relativeCellComplexOfMono.m (base k) d ≫ c₂
    have hh := congrArg (horizontalCurry (SSet.boundary d : SSet.{u})
      (Δ[n] : SSet.{u}) X) (hz s)
    rw [horizontalCurry_pre, horizontalCurry_pre] at hh
    simp only [← Category.assoc, SSet.relativeCellComplexOfMono.ιA_t,
      SSet.relativeCellComplexOfMono.ιA_m]
    simpa only [Category.assoc, c₁, c₂, SSet.relativeCellComplexOfMono.ιB,
      Sigma.ι_desc] using hh.symm
  let hs := SSet.relativeCellComplexOfMono.isPushout (base k) d
  let c := hs.desc c₁ c₂ he
  refine ⟨horizontalUncurry _ _ X c, ?_, ?_⟩
  · apply (horizontalBoxEquiv _ _ X).injective
    change horizontalCurry _ _ X
      (boxMap (step k d) (𝟙 (Δ[n] : SSet.{u})) ≫ horizontalUncurry _ _ X c) = _
    rw [horizontalCurry_pre]
    change step k d ≫ (horizontalBoxEquiv _ _ X) ((horizontalBoxEquiv _ _ X).symm c) = _
    rw [Equiv.apply_symm_apply]
    exact hs.inl_desc c₁ c₂ he
  · intro s
    apply (horizontalBoxEquiv _ _ X).injective
    change horizontalCurry _ _ X
      (boxMap (newFace k d s) (𝟙 (Δ[n] : SSet.{u})) ≫ horizontalUncurry _ _ X c) = _
    rw [horizontalCurry_pre]
    change newFace k d s ≫
      (horizontalBoxEquiv _ _ X) ((horizontalBoxEquiv _ _ X).symm c) = _
    rw [Equiv.apply_symm_apply]
    calc
      newFace k d s ≫ c = SSet.relativeCellComplexOfMono.ιB s ≫
          SSet.relativeCellComplexOfMono.b (base k) d ≫ c := by
        rw [← Category.assoc, SSet.relativeCellComplexOfMono.ιB_b]
      _ = SSet.relativeCellComplexOfMono.ιB s ≫ c₂ := by rw [hs.inr_desc c₁ c₂ he]
      _ = horizontalCurry _ _ X (z s) := Sigma.ι_desc _ _

end
end DaggerNativeDiagonalHornSkeletonGluing
