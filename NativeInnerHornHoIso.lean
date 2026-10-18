import NativeInnerHornFactorization
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Inner horn extensions preserve the actual native homotopy category strictly

Reuse native strict Segal spines and the native ho/nerve adjunction. Inner horn fillers
in a strict Segal target are unique; consequently every actual nerve map is an inner
fibration. Every full inner-left map therefore becomes an isomorphism under ho.
This is not used as a substitute for the full Joyal mapping weak test on all targets.
-/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite SSet
open DaggerNativeInnerHornFactorization
universe u
namespace DaggerNativeInnerHornHoIso
noncomputable section

/-- Restriction to an actual inner horn determines any simplex in a strict Segal target. -/
theorem inner_horn_restriction_injective {X : SSet.{u}} [X.IsStrictSegal]
    (n : ℕ) (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2))
    {f g : Δ[n + 2] ⟶ X} (h : (SSet.horn (n + 2) i).ι ≫ f =
      (SSet.horn (n + 2) i).ι ≫ g) : f = g := by
  apply SSet.yonedaEquiv.injective
  apply (SSet.StrictSegal.ofIsStrictSegal X).spineInjective
  ext k
  simp only [SSet.StrictSegal.spineEquiv, Equiv.coe_fn_mk, SSet.spine_arrow]
  change X.map (SimplexCategory.mkOfSucc k).op
      (f.app (op ⦋n + 2⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 _))) =
    X.map (SimplexCategory.mkOfSucc k).op
      (g.app (op ⦋n + 2⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 _)))
  rw [← FunctorToTypes.naturality, ← FunctorToTypes.naturality]
  exact congrFun (NatTrans.congr_app h (op ⦋1⦌))
    ((SSet.horn.spineId i h0 hn).arrow k)

/-- Any original map of nerves is a full native inner fibration. -/
theorem nerve_map_innerFibration {C D : Cat.{u, u}} (F : C ⟶ D) :
    innerFibrations (nerveFunctor.map F) := by
  intro A B i hi
  obtain ⟨a⟩ := hi
  change HasLiftingProperty (SSet.horn (a.1 + 2) a.2.1).ι (nerveFunctor.map F)
  haveI : (nerveFunctor.obj C).Quasicategory := by
    change (nerve C).Quasicategory
    infer_instance
  haveI : (nerveFunctor.obj D).IsStrictSegal := by
    change (nerve D).IsStrictSegal
    infer_instance
  constructor
  intro f g sq
  obtain ⟨l, hl⟩ := SSet.Quasicategory.hornFilling a.2.2.1 a.2.2.2 f
  refine ⟨l, hl.symm, ?_⟩
  apply inner_horn_restriction_injective a.1 a.2.1 a.2.2.1 a.2.2.2
  rw [← Category.assoc, ← hl, sq.w]

/-- An actual inner-left map becomes left orthogonal to every actual Cat morphism under ho. -/
theorem ho_map_hasLiftingProperty {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i)
    {C D : Cat.{u, u}} (p : C ⟶ D) : HasLiftingProperty (SSet.hoFunctor.map i) p :=
  (nerveAdjunction.hasLiftingProperty_iff i p).2
    (hi (nerveFunctor.map p) (nerve_map_innerFibration p))

/-- Every original inner-left map induces a strict isomorphism of native homotopy categories. -/
theorem ho_map_isIso {X Y : SSet.{u}} (i : X ⟶ Y) (hi : innerAnodyne i) :
    IsIso (SSet.hoFunctor.map i) := by
  haveI := ho_map_hasLiftingProperty i hi (SSet.hoFunctor.map i)
  let sq : CommSq (𝟙 _) (SSet.hoFunctor.map i) (SSet.hoFunctor.map i) (𝟙 _) :=
    ⟨by simp⟩
  exact ⟨⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩

/-- The actual functorial quasi-category unit preserves its native homotopy category strictly. -/
theorem unit_ho_isIso (X : SSet.{u}) :
    IsIso (SSet.hoFunctor.map (unit.app X)) := ho_map_isIso _ (unit_innerAnodyne X)

end
end DaggerNativeInnerHornHoIso
