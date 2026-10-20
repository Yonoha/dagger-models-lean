import Mathlib.CategoryTheory.Limits.Presheaf
import TopCatModelCategory.LeftKanExtensionAlongUliftYoneda
import TopCatModelCategory.FunctorCategoryLimits
import TopCatModelCategory.HasExactColimitsOfShape

universe w w' v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

example : coyoneda (C := C) = yoneda.flip := rfl

namespace Functor

variable (F : C ⥤ Type max w v)

@[simps! obj map]
def functorToCorepresentables : F.Elementsᵒᵖ ⥤ (C ⥤ Type max w v) :=
  (CategoryOfElements.π F).op ⋙ uliftCoyoneda.{w}

@[simps]
def coconeOfCorepresentable : Cocone (functorToCorepresentables F) where
  pt := F
  ι :=
    { app x := uliftCoyonedaEquiv.symm x.unop.2
      naturality x y f := by
        change uliftCoyoneda.map f.unop.val.op ≫ uliftCoyonedaEquiv.symm y.unop.2 =
          uliftCoyonedaEquiv.symm x.unop.2
        rw [← uliftCoyonedaEquiv_symm_map, f.unop.property] }

def colimitOfCorepresentable : IsColimit (coconeOfCorepresentable F) where
  desc s :=
    { app X x := uliftCoyonedaEquiv (s.ι.app (op (Functor.elementsMk F X x)))
      naturality X Y f := by
        ext x
        have := s.w (Quiver.Hom.op (CategoryOfElements.homMk (F.elementsMk X x)
          (F.elementsMk Y (F.map f x)) f rfl))
        dsimp at this x ⊢
        rw [← this, uliftCoyonedaEquiv_comp]
        dsimp
        rw [uliftCoyonedaEquiv_apply, ← FunctorToTypes.naturality,
          uliftCoyonedaEquiv_uliftCoyoneda_map]
        simp [uliftYoneda] }
  fac s j := by
    ext X x
    dsimp
    let φ : j.unop ⟶ (Functor.elementsMk F _
      ((uliftCoyonedaEquiv.symm (unop j).snd).app X x)) := ⟨x.down, rfl⟩
    have := s.w φ.op
    dsimp [φ] at this x ⊢
    rw [← this, uliftCoyonedaEquiv_apply]
    simp [uliftYoneda]
  uniq s m hm := by
    ext X x
    dsimp at hm ⊢
    rw [← hm, uliftCoyonedaEquiv_comp, Equiv.apply_symm_apply]

end Functor

instance {D H : Type*} [Category D] [Category H] (L : C ⥤ D)
    [∀ (F : C ⥤ H), L.HasLeftKanExtension F] :
    (L.lan (H := H)).IsLeftAdjoint :=
  (L.lanAdjunction H).isLeftAdjoint

namespace Presheaf

variable {F : C ⥤ Type max w u v} {G : (Cᵒᵖ ⥤ Type max w u v) ⥤ Type max w u v}

abbrev uliftYonedaUnit (X : Cᵒᵖ) :
    uliftCoyoneda.{max w u}.obj X ⟶
      uliftYoneda.{max w u} ⋙ (evaluation Cᵒᵖ (Type max w u v)).obj X := 𝟙 _

instance (X : Cᵒᵖ) : Functor.IsLeftKanExtension _ (uliftYonedaUnit.{w} X) := by
  rw [isLeftKanExtension_along_uliftYoneda_iff']
  constructor <;> infer_instance

noncomputable def uliftCoyonedaCompUliftYonedaLan :
    uliftCoyoneda.{max w u} ⋙ uliftYoneda.{max w u}.lan ≅
      evaluation Cᵒᵖ (Type max w u v) :=
  NatIso.ofComponents (fun X ↦
    Functor.leftKanExtensionUnique _ ((Functor.lanUnit _).app _) _ (uliftYonedaUnit.{w} X)) (by
      rintro X Y f
      simp only [Functor.leftKanExtensionUnique_hom]
      apply Functor.hom_ext_of_isLeftKanExtension _ ((Functor.lanUnit _).app _)
      have := uliftYoneda.{max w u}.lanUnit.naturality (uliftYoneda.{max w u}.flip.map f)
      dsimp at this ⊢
      rw [Functor.descOfIsLeftKanExtension_fac_assoc, ← reassoc_of% this,
        Functor.descOfIsLeftKanExtension_fac]
      aesop)

instance (X : C) : PreservesFiniteLimits (uliftYoneda.{max w u}.lan.obj
    (uliftCoyoneda.{max w u}.obj (op X))) :=
  preservesFiniteLimits_of_natIso (uliftCoyonedaCompUliftYonedaLan.{w}.symm.app (op X))

open ObjectProperty in
instance [IsCofiltered F.Elements] :
    PreservesFiniteLimits (uliftYoneda.{max w u}.lan.obj F) := by
  rw [← preservesFiniteLimits_iff]
  refine preservesFiniteLimits.prop_of_isColimit
    (isColimitOfPreserves (uliftYoneda.{max w u}.lan)
    (Functor.colimitOfCorepresentable.{max w u} F)) (fun x ↦ by
      rw [preservesFiniteLimits_iff]
      dsimp
      infer_instance)

lemma preservesFiniteLimits_of_isCofiltered_elements
    [IsCofiltered F.Elements] (τ : F ⟶ uliftYoneda.{max w u} ⋙ G)
    [G.IsLeftKanExtension τ] :
    PreservesFiniteLimits G :=
  preservesFiniteLimits_of_natIso
    (Functor.leftKanExtensionUnique _ ((Functor.lanUnit _).app _) _ τ)

end Presheaf

end CategoryTheory
