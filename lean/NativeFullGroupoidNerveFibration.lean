import NativeFullFunctorVertexLifting
import NativeGroupoidNerveHornInjective

/-! Full functors surjective on actual groupoid objects induce genuine native Kan fibrations. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open DaggerNativeFullFunctorVertexLifting DaggerNativeGroupoidNerveHornInjective
open DaggerNativeGroupoidNerveKan
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeFullGroupoidNerveFibration
noncomputable section

theorem one_horn_lifting {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.Full] (hF : Function.Surjective F.obj) (i : Fin 2) :
    HasLiftingProperty (Λ[1, i] : (Δ[1] : SSet.{u}).Subcomplex).ι (nerveMap F) := by
  constructor
  intro a b sq
  let e := SSet.horn₁.iso.{u} i
  have hlp : HasLiftingProperty (e.hom ≫ (Λ[1, i] : (Δ[1] : SSet.{u}).Subcomplex).ι)
      (nerveMap F) := by
    fin_cases i
    · change HasLiftingProperty ((SSet.horn₁.iso (0 : Fin 2)).hom ≫
        (SSet.horn 1 0).ι) (nerveMap F)
      rw [SSet.horn₁.iso₀_hom_ι]
      exact first_vertex_lifting F hF
    · change HasLiftingProperty ((SSet.horn₁.iso (1 : Fin 2)).hom ≫
        (SSet.horn 1 1).ι) (nerveMap F)
      rw [SSet.horn₁.iso₁_hom_ι]
      exact last_vertex_lifting F hF
  let comm : CommSq (e.hom ≫ a) (e.hom ≫ (Λ[1, i] :
      (Δ[1] : SSet.{u}).Subcomplex).ι) (nerveMap F) b :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc]⟩
  refine ⟨comm.lift, ?_, comm.fac_right⟩
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, comm.fac_left]

theorem full_nerve_fibration {C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]
    (F : C ⥤ D) [F.Full] (hF : Function.Surjective F.obj) : Fibration (nerveMap F) := by
  have : (nerve C).KanComplex := nerve_kan C
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  cases n with
  | zero => exact one_horn_lifting F hF i
  | succ n =>
    constructor
    intro a b sq
    obtain ⟨l, hl⟩ := SSet.KanComplex.hornFilling a
    refine ⟨l, hl.symm, ?_⟩
    apply horn_restriction_injective D n i
    rw [← Category.assoc, ← hl, sq.w]

theorem full_nerve_fibration_of_groupoid_categories {C D : Type u}
    [cC : Category.{u} C] [cD : Category.{u} D]
    (hC : ∃ G : Groupoid.{u} C, G.toCategory = cC)
    (hD : ∃ G : Groupoid.{u} D, G.toCategory = cD)
    (F : C ⥤ D) [F.Full] (hF : Function.Surjective F.obj) : Fibration (nerveMap F) := by
  obtain ⟨G, hG⟩ := hC
  obtain ⟨H, hH⟩ := hD
  cases hG
  cases hH
  letI : Groupoid.{u} C := G
  letI : Groupoid.{u} D := H
  exact full_nerve_fibration F hF

end
end DaggerNativeFullGroupoidNerveFibration
