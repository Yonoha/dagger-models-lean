import NativeNerveChainData

/-! Groupoid two-chains are determined by either outside edge and their composite. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeGroupoidTwoChainExt
noncomputable section

theorem first_composite_ext {G : Type u} [Groupoid.{u} G]
    {A B : ComposableArrows G 2}
    (h01 : Arrow.mk (A.map' 0 1) = Arrow.mk (B.map' 0 1))
    (h02 : Arrow.mk (A.map' 0 2) = Arrow.mk (B.map' 0 2)) : A = B := by
  obtain ⟨x0, x1, x2, f, g, rfl⟩ := ComposableArrows.mk₂_surjective A
  obtain ⟨y0, y1, y2, h, k, rfl⟩ := ComposableArrows.mk₂_surjective B
  obtain rfl : x0 = y0 := congrArg Arrow.leftFunc.obj h01
  obtain rfl : x1 = y1 := congrArg Arrow.rightFunc.obj h01
  obtain rfl : x2 = y2 := congrArg Arrow.rightFunc.obj h02
  have hf : f = h := by rw [← Arrow.mk_inj]; exact h01
  cases hf
  have hc : f ≫ g = f ≫ k := by rw [← Arrow.mk_inj]; exact h02
  have hg : g = k := (cancel_epi f).mp hc
  cases hg
  rfl

theorem last_composite_ext {G : Type u} [Groupoid.{u} G]
    {A B : ComposableArrows G 2}
    (h12 : Arrow.mk (A.map' 1 2) = Arrow.mk (B.map' 1 2))
    (h02 : Arrow.mk (A.map' 0 2) = Arrow.mk (B.map' 0 2)) : A = B := by
  obtain ⟨x0, x1, x2, f, g, rfl⟩ := ComposableArrows.mk₂_surjective A
  obtain ⟨y0, y1, y2, h, k, rfl⟩ := ComposableArrows.mk₂_surjective B
  obtain rfl : x1 = y1 := congrArg Arrow.leftFunc.obj h12
  obtain rfl : x2 = y2 := congrArg Arrow.rightFunc.obj h12
  obtain rfl : x0 = y0 := congrArg Arrow.leftFunc.obj h02
  have hg : g = k := by rw [← Arrow.mk_inj]; exact h12
  cases hg
  have hc : f ≫ g = h ≫ g := by rw [← Arrow.mk_inj]; exact h02
  have hf : f = h := (cancel_mono g).mp hc
  cases hf
  rfl

end
end DaggerNativeGroupoidTwoChainExt
