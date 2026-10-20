import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-! A map of simplicial sets with RLP against all monomorphisms has a section and
an actual cylinder homotopy, over its target, from the associated retraction to
the identity. No Kan, model-category, or weak-equivalence hypothesis is used. -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MorphismProperty
  Simplicial Opposite

universe u

namespace DaggerModels.SSetMonoRLPRetraction

noncomputable section

/-- The two literal Mathlib endpoints, combined through the chosen coproduct. -/
def endpoints (X : SSet.{u}) : X ⨿ X ⟶ X ⊗ Δ[1] :=
  coprod.desc SSet.ι₀ SSet.ι₁

@[reassoc (attr := simp)]
lemma inl_endpoints (X : SSet.{u}) : coprod.inl ≫ endpoints X = SSet.ι₀ :=
  coprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma inr_endpoints (X : SSet.{u}) : coprod.inr ≫ endpoints X = SSet.ι₁ :=
  coprod.inr_desc _ _

/-- The endpoint images are disjoint in every simplicial degree. -/
lemma endpoint_app_ne (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) (x y : X.obj m) :
    (SSet.ι₀ : X ⟶ X ⊗ Δ[1]).app m x ≠ (SSet.ι₁ : X ⟶ X ⊗ Δ[1]).app m y := by
  intro h
  have h01 := congrArg (fun z : (X ⊗ Δ[1]).obj m ↦
    z.2.down.toOrderHom (0 : Fin (m.unop.len + 1))) h
  change (0 : Fin 2) = 1 at h01
  exact Fin.zero_ne_one h01

/-- Combining the endpoints on a sum of simplices is injective. -/
lemma endpoint_sum_injective (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    Function.Injective (Sum.elim
      ((SSet.ι₀ : X ⟶ X ⊗ Δ[1]).app m)
      ((SSet.ι₁ : X ⟶ X ⊗ Δ[1]).app m)) := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (congrArg Prod.fst h)
  · exact (endpoint_app_ne X m x y h).elim
  · exact (endpoint_app_ne X m y x h.symm).elim
  · exact congrArg Sum.inr (congrArg Prod.fst h)

/-- The actual two-endpoint inclusion is monic, proved degreewise from disjoint constants. -/
theorem mono_endpoints (X : SSet.{u}) : Mono (endpoints X) := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj m
  have : PreservesColimitsOfShape (Discrete WalkingPair) ev :=
    evaluation_preservesColimitsOfShape m
  let hc := isColimitOfHasBinaryCoproductOfPreservesColimit ev X X
  let hs := Types.binaryCoproductColimit (X.obj m) (X.obj m)
  let e := hs.coconePointUniqueUpToIso hc
  have he : e.hom ≫ (endpoints X).app m =
      Sum.elim ((SSet.ι₀ : X ⟶ X ⊗ Δ[1]).app m)
        ((SSet.ι₁ : X ⟶ X ⊗ Δ[1]).app m) := by
    ext z
    cases z with
    | inl x =>
      have h := congr_fun (hs.comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩) x
      change e.hom (Sum.inl x) = (coprod.inl : X ⟶ X ⨿ X).app m x at h
      simp only [types_comp_apply, h, Sum.elim_inl]
      exact congr_fun (congrArg (fun f : X ⟶ X ⊗ Δ[1] ↦ f.app m) (inl_endpoints X)) x
    | inr x =>
      have h := congr_fun (hs.comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩) x
      change e.hom (Sum.inr x) = (coprod.inr : X ⟶ X ⨿ X).app m x at h
      simp only [types_comp_apply, h, Sum.elim_inr]
      exact congr_fun (congrArg (fun f : X ⟶ X ⊗ Δ[1] ↦ f.app m) (inr_endpoints X)) x
  apply (mono_comp_iff_of_isIso e.hom ((endpoints X).app m)).1
  rw [he, mono_iff_injective]
  exact endpoint_sum_injective X m

/-- RLP against all monomorphisms yields an actual section from the initial lifting square. -/
theorem exists_section {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) : ∃ s : Y ⟶ X, s ≫ p = 𝟙 Y := by
  have : HasLiftingProperty (initial.to Y) p :=
    hp _ (monomorphisms.infer_property _)
  let sq : CommSq (initial.to X) (initial.to Y) p (𝟙 Y) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_right⟩

/-- The same section admits a cylinder homotopy over the target from its retraction to `id`. -/
theorem exists_section_homotopy {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    ∃ (s : Y ⟶ X) (H : X ⊗ Δ[1] ⟶ X),
      s ≫ p = 𝟙 Y ∧ SSet.ι₀ ≫ H = p ≫ s ∧ SSet.ι₁ ≫ H = 𝟙 X ∧
        H ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p := by
  obtain ⟨s, hs⟩ := exists_section p hp
  have : Mono (endpoints X) := mono_endpoints X
  have : HasLiftingProperty (endpoints X) p :=
    hp _ (monomorphisms.infer_property _)
  let sq : CommSq (coprod.desc (p ≫ s) (𝟙 X)) (endpoints X) p
      (CartesianMonoidalCategory.fst X Δ[1] ≫ p) := ⟨by
    apply coprod.hom_ext <;> simp [Category.assoc, hs]⟩
  refine ⟨s, sq.lift, hs, ?_, ?_, sq.fac_right⟩
  · have h := congrArg (fun f : X ⨿ X ⟶ X ↦ coprod.inl ≫ f) sq.fac_left
    simpa only [← Category.assoc, inl_endpoints, coprod.inl_desc] using h
  · have h := congrArg (fun f : X ⨿ X ⟶ X ↦ coprod.inr ≫ f) sq.fac_left
    simpa only [← Category.assoc, inr_endpoints, coprod.inr_desc] using h

end

end DaggerModels.SSetMonoRLPRetraction
