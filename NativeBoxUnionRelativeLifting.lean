import NativeBisimplicialBoxUnionDesc
import NativeBisimplicialBoxHom

/-! Actual union lifting recovers the original relative matching lifting problem. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxHom DaggerNativeBisimplicialBoxUnion
open DaggerNativeBisimplicialBoxUnionDesc
universe u
namespace DaggerNativeBoxUnionRelativeLifting
noncomputable section

theorem curry_uncurry (K A : SSet.{u}) (X : BiSSet.{u})
    (f : A ⟶ horizontalMapping K X) : boxCurry K A X (boxUncurry K A X f) = f :=
  (boxHomEquiv K A X).apply_symm_apply f

theorem union_hom_ext {K B : SSet.{u}} (H : K.Subcomplex) (A : B.Subcomplex)
    {X : BiSSet.{u}} {f g : boxUnion H A ⟶ X}
    (hh : horizontalInclusion H A ≫ f = horizontalInclusion H A ≫ g)
    (hv : verticalInclusion H A ≫ f = verticalInclusion H A ≫ g) : f = g := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  funext v p
  rcases union_cover H A h v p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · exact congrFun (NatTrans.congr_app (NatTrans.congr_app hh h) v) q
  · exact congrFun (NatTrans.congr_app (NatTrans.congr_app hv h) v) q

theorem relative_lifting_of_union {K B : SSet.{u}} (H : K.Subcomplex) (A : B.Subcomplex)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : HasLiftingProperty (unionInclusion H A) f) :
    HasLiftingProperty A.ι (relativeRestriction H.ι f) := by
  constructor
  intro a b sq
  let b₁ := b ≫ pullback.fst (horizontalMap (H : SSet.{u}) f) (horizontalPre H.ι Y)
  let b₂ := b ≫ pullback.snd (horizontalMap (H : SSet.{u}) f) (horizontalPre H.ι Y)
  have h₁ : a ≫ horizontalPre H.ι X = A.ι ≫ b₁ := by
    have hh := congrArg (fun t ↦ t ≫
      pullback.fst (horizontalMap (H : SSet.{u}) f) (horizontalPre H.ι Y)) sq.w
    simpa only [Category.assoc, relativeRestriction_fst, b₁] using hh
  have h₂ : a ≫ horizontalMap K f = A.ι ≫ b₂ := by
    have hh := congrArg (fun t ↦ t ≫
      pullback.snd (horizontalMap (H : SSet.{u}) f) (horizontalPre H.ι Y)) sq.w
    simpa only [Category.assoc, relativeRestriction_snd, b₂] using hh
  have h₃ : b₁ ≫ horizontalMap (H : SSet.{u}) f = b₂ ≫ horizontalPre H.ι Y := by
    dsimp only [b₁, b₂]
    rw [Category.assoc, pullback.condition, Category.assoc]
  let av := boxUncurry K (A : SSet.{u}) X a
  let bh := boxUncurry (H : SSet.{u}) B X b₁
  let c := boxUncurry K B Y b₂
  have hc : boxMap H.ι (𝟙 (A : SSet.{u})) ≫ av =
      boxMap (𝟙 (H : SSet.{u})) A.ι ≫ bh := by
    apply (boxHomEquiv (H : SSet.{u}) (A : SSet.{u}) X).injective
    change boxCurry _ _ X (boxMap H.ι (𝟙 (A : SSet.{u})) ≫ av) =
      boxCurry _ _ X (boxMap (𝟙 (H : SSet.{u})) A.ι ≫ bh)
    rw [boxCurry_pre, boxCurry_pre, horizontalPre_id, Category.id_comp, Category.comp_id]
    simpa only [av, bh, curry_uncurry] using h₁
  have hv : av ≫ f = boxMap (𝟙 K) A.ι ≫ c := by
    apply (boxHomEquiv K (A : SSet.{u}) Y).injective
    change boxCurry _ _ Y (av ≫ f) = boxCurry _ _ Y (boxMap (𝟙 K) A.ι ≫ c)
    rw [boxCurry_post, boxCurry_pre, horizontalPre_id, Category.comp_id]
    simpa only [av, c, curry_uncurry] using h₂
  have hh : bh ≫ f = boxMap H.ι (𝟙 B) ≫ c := by
    apply (boxHomEquiv (H : SSet.{u}) B Y).injective
    change boxCurry _ _ Y (bh ≫ f) = boxCurry _ _ Y (boxMap H.ι (𝟙 B) ≫ c)
    rw [boxCurry_post, boxCurry_pre, Category.id_comp]
    simpa only [bh, c, curry_uncurry] using h₃
  let u := unionDesc H A av bh hc
  have ss : CommSq u (unionInclusion H A) f c := by
    constructor
    apply union_hom_ext H A
    · simpa only [← Category.assoc, u, horizontalInclusion_desc,
        horizontalInclusion_comp] using hh
    · simpa only [← Category.assoc, u, verticalInclusion_desc,
        verticalInclusion_comp] using hv
  have : HasLiftingProperty (unionInclusion H A) f := hf
  have hleft : boxMap (𝟙 K) A.ι ≫ ss.lift = av := by
    have he := congrArg (fun t ↦ verticalInclusion H A ≫ t) ss.fac_left
    simpa only [← Category.assoc, verticalInclusion_comp, u,
      verticalInclusion_desc] using he
  have hboundary : boxMap H.ι (𝟙 B) ≫ ss.lift = bh := by
    have he := congrArg (fun t ↦ horizontalInclusion H A ≫ t) ss.fac_left
    simpa only [← Category.assoc, horizontalInclusion_comp, u,
      horizontalInclusion_desc] using he
  refine ⟨boxCurry K B X ss.lift, ?_, ?_⟩
  · have he := congrArg (boxCurry K (A : SSet.{u}) X) hleft
    rw [boxCurry_pre, horizontalPre_id, Category.comp_id] at he
    simpa only [av, curry_uncurry] using he
  · apply pullback.hom_ext
    · simp only [Category.assoc, relativeRestriction_fst]
      have he := congrArg (boxCurry (H : SSet.{u}) B X) hboundary
      rw [boxCurry_pre, Category.id_comp] at he
      simpa only [bh, b₁, curry_uncurry] using he
    · simp only [Category.assoc, relativeRestriction_snd]
      have he := congrArg (boxCurry K B Y) ss.fac_right
      rw [boxCurry_post] at he
      simpa only [c, b₂, curry_uncurry] using he

end
end DaggerNativeBoxUnionRelativeLifting
