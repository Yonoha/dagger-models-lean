import NativeBisimplicialBox

/-! The actual union of the horizontal boundary box and the vertical subobject box. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
universe u
namespace DaggerNativeBisimplicialBoxUnion
noncomputable section

variable {K B : SSet.{u}} (H : K.Subcomplex) (A : B.Subcomplex)

def unionRow (h : SimplexCategoryᵒᵖ) : (boxRow (K.obj h) B).Subcomplex where
  obj v p := p.1 ∈ H.obj h ∨ p.2 ∈ A.obj v
  map β _ hp := hp.imp id (fun ht ↦ A.map β ht)

def boxUnion : BiSSet.{u} where
  obj h := unionRow H A h
  map α :=
    { app := fun _ p ↦ ⟨(K.map α p.val.1, p.val.2), p.property.imp (fun ht ↦ H.map α ht) id⟩
      naturality := by intros; funext p; apply Subtype.ext; rfl }
  map_id h := by
    apply NatTrans.ext
    funext v p
    apply Subtype.ext
    change (K.map (𝟙 h) p.val.1, p.val.2) = p.val
    rw [K.map_id]
    rfl
  map_comp α β := by
    apply NatTrans.ext
    funext v p
    apply Subtype.ext
    change (K.map (α ≫ β) p.val.1, p.val.2) = _
    rw [K.map_comp]
    rfl

def unionInclusion : boxUnion H A ⟶ box K B where
  app h := (unionRow H A h).ι
  naturality _ _ _ := by apply NatTrans.ext; rfl

def horizontalInclusion : box (H : SSet.{u}) B ⟶ boxUnion H A where
  app _ :=
    { app := fun _ p ↦ ⟨(p.1.val, p.2), Or.inl p.1.property⟩
      naturality := by intros; funext p; apply Subtype.ext; rfl }
  naturality _ _ _ := by apply NatTrans.ext; funext v p; apply Subtype.ext; rfl

def verticalInclusion : box K (A : SSet.{u}) ⟶ boxUnion H A where
  app _ :=
    { app := fun _ p ↦ ⟨(p.1, p.2.val), Or.inr p.2.property⟩
      naturality := by intros; funext p; apply Subtype.ext; rfl }
  naturality _ _ _ := by apply NatTrans.ext; funext v p; apply Subtype.ext; rfl

theorem horizontalInclusion_comp : horizontalInclusion H A ≫ unionInclusion H A =
    boxMap H.ι (𝟙 B) := by apply NatTrans.ext; funext h; apply NatTrans.ext; rfl

theorem verticalInclusion_comp : verticalInclusion H A ≫ unionInclusion H A =
    boxMap (𝟙 K) A.ι := by apply NatTrans.ext; funext h; apply NatTrans.ext; rfl

theorem intersection_square :
    boxMap H.ι (𝟙 (A : SSet.{u})) ≫ verticalInclusion H A =
      boxMap (𝟙 (H : SSet.{u})) A.ι ≫ horizontalInclusion H A := by
  apply NatTrans.ext
  funext h
  apply NatTrans.ext
  funext v p
  apply Subtype.ext
  rfl

theorem unionInclusion_mono : Mono (unionInclusion H A) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro h
  change Mono (unionRow H A h).ι
  infer_instance

end
end DaggerNativeBisimplicialBoxUnion
