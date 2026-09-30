import DaggerModels.FreeDaggerPushout

/-!
# The literal zero-skeleton pushout formula

This transfers the discrete-vertices presentation along its proved canonical
isomorphism to the zero-skeleton subcomplex. In mathlib's indexing that is
`skeleton 1`, corresponding to `sk₀` in Part I, `dj.not.adjunctions`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace DaggerModels

/-- The free completion is the pushout over the actual zero-skeleton, with its
unit and swap dagger, for any choice of the free--forgetful adjunction. -/
theorem freeDagger_skeleton_pushout (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget.{u}) :
    ∃ r : SSet.opFunctor ⟶ F ⋙ DaggerSSet.forget, ∀ A,
      ∃ e : SSetVertices.obj A ≅ (A.skeleton 1).toSSet,
        e.hom ≫ (A.skeleton 1).ι = SSetVertices.inclusion A ∧
        IsPushout (A.skeleton 1).ι (e.inv ≫ SSetVertices.opInclusion A)
          (adj.unit.app A) (r.app A) ∧
        (adj.unit.app A ≫ (F.obj A).dagger =
          (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map (r.app A)) ∧
        (r.app A ≫ (F.obj A).dagger = SSet.opFunctor.map (adj.unit.app A)) := by
  obtain ⟨r, hr⟩ := freeDagger_pushout F adj
  refine ⟨r, fun A ↦ ⟨SSetVertices.skeletonIso A,
    SSetVertices.skeletonIso_hom_inclusion A, ?_, (hr A).2⟩⟩
  apply (hr A).1.of_iso (SSetVertices.skeletonIso A) (Iso.refl A)
    (Iso.refl A.op) (Iso.refl ((F.obj A).toSSet))
  · simp
  · simp
  · ext n x
    rfl
  · ext n x
    rfl

end DaggerModels
