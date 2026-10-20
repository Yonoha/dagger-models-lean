import NativeGroupoidNerveKan

/-! Full functors surjective on objects lift both actual vertex inclusions into the nerve. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerNativeFullFunctorVertexLifting
noncomputable section

theorem first_vertex_lifting {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Full] (hF : Function.Surjective F.obj) :
    HasLiftingProperty (SSet.stdSimplex.δ (1 : Fin 2)) (nerveMap F) := by
  constructor
  intro a b sq
  obtain ⟨A, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective A
  obtain ⟨B, rfl⟩ := SSet.yonedaEquiv.symm.surjective b
  obtain ⟨d0, d1, f, rfl⟩ := ComposableArrows.mk₁_surjective B
  have hx : F.obj x = d0 :=
    congrArg (fun q ↦ nerveEquiv (SSet.yonedaEquiv q)) sq.w
  subst d0
  obtain ⟨y, hy⟩ := hF d1
  subst d1
  obtain ⟨g, hg⟩ := F.map_surjective f
  refine ⟨SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g), ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    exact ComposableArrows.ext₀ rfl
  · apply SSet.yonedaEquiv.injective
    exact ComposableArrows.ext₁ rfl rfl (by simpa using hg)

theorem last_vertex_lifting {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Full] (hF : Function.Surjective F.obj) :
    HasLiftingProperty (SSet.stdSimplex.δ (0 : Fin 2)) (nerveMap F) := by
  constructor
  intro a b sq
  obtain ⟨A, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
  obtain ⟨x, rfl⟩ := nerveEquiv.symm.surjective A
  obtain ⟨B, rfl⟩ := SSet.yonedaEquiv.symm.surjective b
  obtain ⟨d0, d1, f, rfl⟩ := ComposableArrows.mk₁_surjective B
  have hx : F.obj x = d1 :=
    congrArg (fun q ↦ nerveEquiv (SSet.yonedaEquiv q)) sq.w
  subst d1
  obtain ⟨y, hy⟩ := hF d0
  subst d0
  obtain ⟨g, hg⟩ := F.map_surjective f
  refine ⟨SSet.yonedaEquiv.symm (ComposableArrows.mk₁ g), ?_, ?_⟩
  · apply SSet.yonedaEquiv.injective
    exact ComposableArrows.ext₀ rfl
  · apply SSet.yonedaEquiv.injective
    exact ComposableArrows.ext₁ rfl rfl (by simpa using hg)

end
end DaggerNativeFullFunctorVertexLifting
