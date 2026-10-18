import NativeBisimplicialHorizontalTranspose

/-! Exchange the actual relative lifting problems in the two simplicial directions. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialHorizontalTranspose
universe u
namespace DaggerNativeBisimplicialRelativeLifting
noncomputable section

abbrev flipMap {X Y : BiSSet.{u}} (f : X ⟶ Y) : X.flip ⟶ Y.flip :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map f

theorem relative_lifting_of_transpose {K L A B : SSet.{u}} (i : K ⟶ L) (j : A ⟶ B)
    {X Y : BiSSet.{u}} (f : X ⟶ Y)
    (h : HasLiftingProperty i (relativeRestriction j (flipMap f))) :
    HasLiftingProperty j (relativeRestriction i f) := by
  constructor
  intro a b sq
  let b₁ := b ≫ pullback.fst (horizontalMap K f) (horizontalPre i Y)
  let b₂ := b ≫ pullback.snd (horizontalMap K f) (horizontalPre i Y)
  have h₁ : a ≫ horizontalPre i X = j ≫ b₁ := by
    have hh := congrArg
      (fun t ↦ t ≫ pullback.fst (horizontalMap K f) (horizontalPre i Y)) sq.w
    simpa only [Category.assoc, relativeRestriction_fst, b₁] using hh
  have h₂ : a ≫ horizontalMap L f = j ≫ b₂ := by
    have hh := congrArg
      (fun t ↦ t ≫ pullback.snd (horizontalMap K f) (horizontalPre i Y)) sq.w
    simpa only [Category.assoc, relativeRestriction_snd, b₂] using hh
  have h₃ : b₁ ≫ horizontalMap K f = b₂ ≫ horizontalPre i Y := by
    dsimp only [b₁, b₂]
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hc : transpose L A X a ≫ horizontalMap A (flipMap f) =
      transpose L B Y b₂ ≫ horizontalPre j Y.flip := by
    have hh := congrArg (transpose L A Y) h₂
    simpa only [transpose_post, transpose_pre_vertical] using hh
  let d := pullback.lift (transpose L A X a) (transpose L B Y b₂) hc
  have sd : CommSq (transpose K B X b₁) i (relativeRestriction j (flipMap f)) d := by
    constructor
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeRestriction_fst, d, pullback.lift_fst]
      have hh := congrArg (transpose K A X) h₁
      simpa only [transpose_pre_horizontal, transpose_pre_vertical] using hh.symm
    · simp only [Category.assoc, relativeRestriction_snd, d, pullback.lift_snd]
      have hh := congrArg (transpose K B Y) h₃
      simpa only [transpose_post, transpose_pre_horizontal] using hh
  have : HasLiftingProperty i (relativeRestriction j (flipMap f)) := h
  have hcanc : transpose L B X (transpose B L X.flip sd.lift) = sd.lift :=
    (transposeEquiv L B X).apply_symm_apply sd.lift
  refine ⟨transpose B L X.flip sd.lift, ?_, ?_⟩
  · apply (transposeEquiv L A X).injective
    change transpose L A X (j ≫ transpose B L X.flip sd.lift) = transpose L A X a
    rw [transpose_pre_vertical, hcanc]
    have hh := congrArg
      (fun t ↦ t ≫ pullback.fst (horizontalMap A (flipMap f))
        (horizontalPre j Y.flip)) sd.fac_right
    simpa only [Category.assoc, relativeRestriction_fst, d, pullback.lift_fst] using hh
  · apply pullback.hom_ext
    · simp only [Category.assoc, relativeRestriction_fst]
      apply (transposeEquiv K B X).injective
      change transpose K B X
        (transpose B L X.flip sd.lift ≫ horizontalPre i X) = transpose K B X b₁
      rw [transpose_pre_horizontal, hcanc]
      exact sd.fac_left
    · simp only [Category.assoc, relativeRestriction_snd]
      apply (transposeEquiv L B Y).injective
      change transpose L B Y
        (transpose B L X.flip sd.lift ≫ horizontalMap L f) = transpose L B Y b₂
      rw [transpose_post, transpose_involutive]
      have hh := congrArg
        (fun t ↦ t ≫ pullback.snd (horizontalMap A (flipMap f))
          (horizontalPre j Y.flip)) sd.fac_right
      simpa only [Category.assoc, relativeRestriction_snd, d, pullback.lift_snd] using hh

theorem relative_lifting_iff {K L A B : SSet.{u}} (i : K ⟶ L) (j : A ⟶ B)
    {X Y : BiSSet.{u}} (f : X ⟶ Y) :
    HasLiftingProperty j (relativeRestriction i f) ↔
      HasLiftingProperty i (relativeRestriction j (flipMap f)) :=
  ⟨relative_lifting_of_transpose j i (flipMap f), relative_lifting_of_transpose i j f⟩

end
end DaggerNativeBisimplicialRelativeLifting
