import OriginalTaggedReverseSimplex
import DaggerModels.NormalCofibrationObstruction

/-!
# Anti-involutive simplicial sets as tagged reversal presheaves

The tag is not identified in degree zero. Consequently no fixed-vertex
condition is used or obtained by this equivalence.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels

open OriginalTaggedReverseSimplex
open TaggedReverseSimplex

namespace AntiInvolutiveSSet

@[simp]
theorem dagger_dagger (X : AntiInvolutiveSSet.{u}) {n : ℕ}
    (x : X.toSSet _⦋n⦌) : X.daggerSimplex (X.daggerSimplex x) = x :=
  X.involutive n x

theorem dagger_map (X : AntiInvolutiveSSet.{u}) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (x : X.toSSet _⦋n⦌) :
    X.daggerSimplex (X.toSSet.map f.op x) =
      X.toSSet.map (SimplexCategory.rev.map f).op (X.daggerSimplex x) := by
  simpa [AntiInvolutiveSSet.daggerSimplex, SSet.op_map, SSet.opObjEquiv] using
    congrFun (X.dagger.naturality f.op) x

/-- The two normal-form actions, including the true tag in degree zero. -/
def extensionMap (X : AntiInvolutiveSSet.{u}) {m n : TaggedReverseSimplex}
    (f : m ⟶ n) (x : X.toSSet _⦋n.len⦌) : X.toSSet _⦋m.len⦌ :=
  X.toSSet.map f.base.op (if f.tag then X.daggerSimplex x else x)

theorem extensionMap_id (X : AntiInvolutiveSSet.{u})
    (m : TaggedReverseSimplex) (x : X.toSSet _⦋m.len⦌) :
    X.extensionMap (𝟙 m) x = x := by
  change X.toSSet.map (𝟙 ⦋m.len⦌).op x = x
  simp

theorem extensionMap_comp (X : AntiInvolutiveSSet.{u})
    {l m n : TaggedReverseSimplex} (f : l ⟶ m) (g : m ⟶ n)
    (x : X.toSSet _⦋n.len⦌) :
    X.extensionMap (f ≫ g) x = X.extensionMap f (X.extensionMap g x) := by
  cases f with
  | mk α a =>
    cases g with
    | mk β b =>
      cases a <;> cases b
      · change X.toSSet.map (α ≫ β).op x =
          X.toSSet.map α.op (X.toSSet.map β.op x)
        rw [op_comp, X.toSSet.map_comp]
        rfl
      · change X.toSSet.map (α ≫ β).op (X.daggerSimplex x) =
          X.toSSet.map α.op (X.toSSet.map β.op (X.daggerSimplex x))
        rw [op_comp, X.toSSet.map_comp]
        rfl
      · change X.toSSet.map (α ≫ SimplexCategory.rev.map β).op
          (X.daggerSimplex x) =
            X.toSSet.map α.op (X.daggerSimplex (X.toSSet.map β.op x))
        rw [X.dagger_map β x, op_comp, X.toSSet.map_comp]
        rfl
      · change X.toSSet.map (α ≫ SimplexCategory.rev.map β).op x =
          X.toSSet.map α.op
            (X.daggerSimplex (X.toSSet.map β.op (X.daggerSimplex x)))
        rw [X.dagger_map β (X.daggerSimplex x), X.dagger_dagger,
          op_comp, X.toSSet.map_comp]
        rfl

/-- Extension of the original anti-involutive simplicial set to tagged maps. -/
def extension (X : AntiInvolutiveSSet.{u}) :
    TaggedReverseSimplexᵒᵖ ⥤ Type u where
  obj n := X.toSSet _⦋n.unop.len⦌
  map f := X.extensionMap f.unop
  map_id n := by
    funext x
    exact X.extensionMap_id n.unop x
  map_comp f g := by
    funext x
    exact X.extensionMap_comp g.unop f.unop x

theorem extension_inclusion (X : AntiInvolutiveSSet.{u})
    {m n : SimplexCategory} (f : m ⟶ n) (x : X.toSSet.obj (op n)) :
    X.extension.map (simplexInclusion.map f).op x = X.toSSet.map f.op x := rfl

theorem extension_reversal (X : AntiInvolutiveSSet.{u})
    (n : TaggedReverseSimplex) (x : X.toSSet _⦋n.len⦌) :
    X.extension.map (taggedReversal n).op x = X.daggerSimplex x := by
  change X.toSSet.map (𝟙 ⦋n.len⦌).op (X.daggerSimplex x) = _
  simp

theorem Hom.dagger_comm {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y)
    {n : ℕ} (x : X.toSSet _⦋n⦌) :
    f.hom.app (op ⦋n⦌) (X.daggerSimplex x) =
      Y.daggerSimplex (f.hom.app (op ⦋n⦌) x) := by
  exact (congrFun (NatTrans.congr_app f.comm (op ⦋n⦌)) x).symm

theorem Hom.extensionMap_naturality {X Y : AntiInvolutiveSSet.{u}}
    (f : X ⟶ Y) {m n : TaggedReverseSimplex} (g : m ⟶ n)
    (x : X.toSSet _⦋n.len⦌) :
    f.hom.app (op ⦋m.len⦌) (X.extensionMap g x) =
      Y.extensionMap g (f.hom.app (op ⦋n.len⦌) x) := by
  cases g with
  | mk α tag =>
    cases tag
    · exact congrFun (f.hom.naturality α.op) x
    · change f.hom.app (op ⦋m.len⦌)
        (X.toSSet.map α.op (X.daggerSimplex x)) =
          Y.toSSet.map α.op (Y.daggerSimplex (f.hom.app (op ⦋n.len⦌) x))
      have h := congrFun (f.hom.naturality α.op) (X.daggerSimplex x)
      change f.hom.app (op ⦋m.len⦌)
        (X.toSSet.map α.op (X.daggerSimplex x)) =
          Y.toSSet.map α.op
            (f.hom.app (op ⦋n.len⦌) (X.daggerSimplex x)) at h
      rw [h, f.dagger_comm]

def extensionHom {X Y : AntiInvolutiveSSet.{u}} (f : X ⟶ Y) :
    X.extension ⟶ Y.extension where
  app n := f.hom.app (op ⦋n.unop.len⦌)
  naturality {n m} g := by
    funext x
    exact f.extensionMap_naturality g.unop x

def toPresheaf : AntiInvolutiveSSet.{u} ⥤
    (TaggedReverseSimplexᵒᵖ ⥤ Type u) where
  obj := extension
  map := extensionHom
  map_id X := by ext n x; rfl
  map_comp f g := by ext n x; rfl

end AntiInvolutiveSSet

namespace TaggedPresheaf

/-- Ordinary restriction, with dagger induced by the independent true tag. -/
def restriction (H : TaggedReverseSimplexᵒᵖ ⥤ Type u) :
    AntiInvolutiveSSet.{u} where
  toSSet := simplexInclusion.op ⋙ H
  dagger :=
    { app := fun n ↦ H.map (taggedReversal ⟨n.unop.len⟩).op
      naturality := fun {n m} f ↦ by
        change H.map (simplexInclusion.map f.unop).op ≫
          H.map (taggedReversal ⟨m.unop.len⟩).op =
            H.map (taggedReversal ⟨n.unop.len⟩).op ≫
              H.map (simplexInclusion.map (SimplexCategory.rev.map f.unop)).op
        rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp]
        congr 1 }
  involutive n x := by
    change H.map (taggedReversal ⟨n⟩).op
      (H.map (taggedReversal ⟨n⟩).op x) = x
    have h := congrFun (H.map_comp (taggedReversal ⟨n⟩).op
      (taggedReversal ⟨n⟩).op) x
    simpa only [← op_comp, taggedReversal_sq, op_id, H.map_id] using h.symm

def restrictionHom {H G : TaggedReverseSimplexᵒᵖ ⥤ Type u}
    (f : H ⟶ G) : restriction H ⟶ restriction G where
  hom :=
    { app := fun n ↦ f.app (op (simplexInclusion.obj n.unop))
      naturality {n m} g := f.naturality (simplexInclusion.op.map g) }
  comm := by
    ext n x
    exact (congrFun (f.naturality (taggedReversal ⟨n.unop.len⟩).op) x).symm

def toAntiInvolutive : (TaggedReverseSimplexᵒᵖ ⥤ Type u) ⥤
    AntiInvolutiveSSet.{u} where
  obj := restriction
  map := restrictionHom
  map_id H := by apply AntiInvolutiveSSet.Hom.ext; rfl
  map_comp f g := by apply AntiInvolutiveSSet.Hom.ext; rfl

theorem restriction_extension (H : TaggedReverseSimplexᵒᵖ ⥤ Type u)
    {m n : TaggedReverseSimplex} (f : m ⟶ n) (x : H.obj (op n)) :
    (restriction H).extension.map f.op x = H.map f.op x := by
  cases f with
  | mk α tag =>
    cases tag
    · rfl
    · change H.map (simplexInclusion.map α).op
        (H.map (taggedReversal ⟨n.len⟩).op x) =
          H.map (Quiver.Hom.op (⟨α, true⟩ : m ⟶ n)) x
      have h := congrFun (H.map_comp (taggedReversal ⟨n.len⟩).op
        (simplexInclusion.map α).op) x
      simp only [types_comp_apply] at h
      rw [← h, ← op_comp]
      have hc : simplexInclusion.map α ≫ taggedReversal ⟨n.len⟩ =
          (⟨α, true⟩ : m ⟶ n) := by
        change (⟨α ≫ 𝟙 _, true⟩ : m ⟶ n) = (⟨α, true⟩ : m ⟶ n)
        rw [Category.comp_id]
      rw [hc]

end TaggedPresheaf

namespace AntiInvolutiveSSet

def unitComponent (X : AntiInvolutiveSSet.{u}) :
    X ≅ TaggedPresheaf.restriction X.extension where
  hom :=
    { hom :=
        { app := fun _ ↦ id
          naturality := fun {n m} f ↦ by
            funext x
            exact (X.extension_inclusion f.unop x).symm }
      comm := by
        ext n x
        exact X.extension_reversal ⟨n.unop.len⟩ x }
  inv :=
    { hom :=
        { app := fun _ ↦ id
          naturality := fun {n m} f ↦ by
            funext x
            exact X.extension_inclusion f.unop x }
      comm := by
        ext n x
        exact (X.extension_reversal ⟨n.unop.len⟩ x).symm }
  hom_inv_id := by apply Hom.ext; ext n x; rfl
  inv_hom_id := by apply Hom.ext; ext n x; rfl

def unitIso :
    𝟭 AntiInvolutiveSSet.{u} ≅
      toPresheaf ⋙ TaggedPresheaf.toAntiInvolutive :=
  NatIso.ofComponents unitComponent (by
    intro X Y f
    apply Hom.ext
    ext n x
    rfl)

end AntiInvolutiveSSet

namespace TaggedPresheaf

def counitComponent (H : TaggedReverseSimplexᵒᵖ ⥤ Type u) :
    (restriction H).extension ≅ H where
  hom :=
    { app := fun _ ↦ id
      naturality := fun {n m} f ↦ by
        funext x
        exact restriction_extension H f.unop x }
  inv :=
    { app := fun _ ↦ id
      naturality := fun {n m} f ↦ by
        funext x
        exact (restriction_extension H f.unop x).symm }
  hom_inv_id := by ext n x; rfl
  inv_hom_id := by ext n x; rfl

def counitIso :
    toAntiInvolutive ⋙ AntiInvolutiveSSet.toPresheaf ≅
      𝟭 (TaggedReverseSimplexᵒᵖ ⥤ Type u) :=
  NatIso.ofComponents counitComponent (by
    intro H G f
    ext n x
    rfl)

end TaggedPresheaf

/-- The actual tagged category presents anti-involutive simplicial sets. -/
def antiInvolutiveEquivalence :
    AntiInvolutiveSSet.{u} ≌ (TaggedReverseSimplexᵒᵖ ⥤ Type u) where
  functor := AntiInvolutiveSSet.toPresheaf
  inverse := TaggedPresheaf.toAntiInvolutive
  unitIso := AntiInvolutiveSSet.unitIso
  counitIso := TaggedPresheaf.counitIso
  functor_unitIso_comp X := by ext n x; rfl

end DaggerModels
