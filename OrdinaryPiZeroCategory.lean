import DaggerModels.SimplicialEnrichment
import TopCatModelCategory.SSet.PiZero
import Mathlib.CategoryTheory.Quotient

set_option autoImplicit false
set_option maxHeartbeats 0
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels

universe o o₂ o₃ v

namespace DaggerOrdinaryPiZeroCategory

/-- The original degree-zero category, without changing its vertices or composition. -/
abbrev V (C : SimplicialCat.{o, v}) := SimplicialEnrichment.At C.Obj (op ⦋0⦌)

/-- Original pi0 equality as a relation on the original degree-zero arrows. -/
def vertexRel (C : SimplicialCat.{o, v}) : HomRel (V C) :=
  fun _ _ f g ↦ SSet.π₀.mk f = SSet.π₀.mk g

private theorem comp_left_piZero (C : SimplicialCat.{o, v})
    {x y z : V C} (f : x ⟶ y) {g g' : y ⟶ z}
    (h : SSet.π₀.mk g = SSet.π₀.mk g') :
    SSet.π₀.mk (f ≫ g) = SSet.π₀.mk (f ≫ g') := by
  have he := (SSet.π₀.mk_eq_mk_iff g g').1 h
  clear h
  induction he with
  | rel a b h =>
    rcases h with ⟨e, ha, hb⟩
    apply SSet.π₀.sound ((C.enriched.comp x y z).app (op ⦋1⦌)
      ((C.enriched.Hom x y).σ 0 f, e))
    · change (C.enriched.Hom x z).δ 1
        ((C.enriched.comp x y z).app _ (_, e)) = _
      rw [← SSet.δ_naturality_apply]
      change (C.enriched.comp x y z).app _
        ((C.enriched.Hom x y).δ 1 ((C.enriched.Hom x y).σ 0 f),
          (C.enriched.Hom y z).δ 1 e) = _
      rw [ha]
      exact congrArg (fun v ↦ (C.enriched.comp x y z).app _ (v, a))
        (congrFun ((C.enriched.Hom x y).δ_comp_σ_succ (i := 0)) f)
    · change (C.enriched.Hom x z).δ 0
        ((C.enriched.comp x y z).app _ (_, e)) = _
      rw [← SSet.δ_naturality_apply]
      change (C.enriched.comp x y z).app _
        ((C.enriched.Hom x y).δ 0 ((C.enriched.Hom x y).σ 0 f),
          (C.enriched.Hom y z).δ 0 e) = _
      rw [hb]
      exact congrArg (fun v ↦ (C.enriched.comp x y z).app _ (v, b))
        (congrFun ((C.enriched.Hom x y).δ_comp_σ_self (i := 0)) f)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

private theorem comp_right_piZero (C : SimplicialCat.{o, v})
    {x y z : V C} (g : y ⟶ z) {f f' : x ⟶ y}
    (h : SSet.π₀.mk f = SSet.π₀.mk f') :
    SSet.π₀.mk (f ≫ g) = SSet.π₀.mk (f' ≫ g) := by
  have he := (SSet.π₀.mk_eq_mk_iff f f').1 h
  clear h
  induction he with
  | rel a b h =>
    rcases h with ⟨e, ha, hb⟩
    apply SSet.π₀.sound ((C.enriched.comp x y z).app (op ⦋1⦌)
      (e, (C.enriched.Hom y z).σ 0 g))
    · rw [← SSet.δ_naturality_apply]
      change (C.enriched.comp x y z).app _ ((C.enriched.Hom x y).δ 1 e,
        (C.enriched.Hom y z).δ 1 ((C.enriched.Hom y z).σ 0 g)) = _
      rw [ha]
      exact congrArg (fun v ↦ (C.enriched.comp x y z).app _ (a, v))
        (congrFun ((C.enriched.Hom y z).δ_comp_σ_succ (i := 0)) g)
    · rw [← SSet.δ_naturality_apply]
      change (C.enriched.comp x y z).app _ ((C.enriched.Hom x y).δ 0 e,
        (C.enriched.Hom y z).δ 0 ((C.enriched.Hom y z).σ 0 g)) = _
      rw [hb]
      exact congrArg (fun v ↦ (C.enriched.comp x y z).app _ (b, v))
        (congrFun ((C.enriched.Hom y z).δ_comp_σ_self (i := 0)) g)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

instance vertexRel_congruence (C : SimplicialCat.{o, v}) :
    CategoryTheory.Congruence (vertexRel C) where
  comp_left {_ _ _} f {_ _} h := comp_left_piZero C f h
  comp_right {_ _ _} {_ _} g h := comp_right_piZero C g h
  equivalence := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h h' ↦ h.trans h'⟩

/-- Both directions identify the actual categorical quotient Hom with the original pi0. -/
def quotientHomEquiv (C : SimplicialCat.{o, v}) (x y : V C) :
    ((CategoryTheory.Quotient.functor (vertexRel C)).obj x ⟶
      (CategoryTheory.Quotient.functor (vertexRel C)).obj y) ≃
        SSet.π₀ (C.enriched.Hom x y) where
  toFun := Quot.lift SSet.π₀.mk (fun f g h ↦
    (HomRel.compClosure_iff_self (vertexRel C) f g).1 h)
  invFun := Quot.lift (fun f ↦ Quot.mk _ f) (by
    rintro f g ⟨e, hf, hg⟩
    exact Quot.sound (HomRel.CompClosure.of (SSet.π₀.sound e hf hg)))
  left_inv := fun q ↦ Quot.inductionOn q (fun _ ↦ rfl)
  right_inv := fun q ↦ Quot.inductionOn q (fun _ ↦ rfl)

/-- Objects are original objects; Hom sets are literally the original pi0 Hom sets. -/
def hC (C : SimplicialCat.{o, v}) : Type o := C.Obj

instance hC_category (C : SimplicialCat.{o, v}) : Category (hC C) where
  Hom x y := SSet.π₀ (C.enriched.Hom x y)
  id x := quotientHomEquiv C x x (𝟙 _)
  comp {x y z} f g := quotientHomEquiv C x z
    ((quotientHomEquiv C x y).symm f ≫ (quotientHomEquiv C y z).symm g)
  id_comp {x y} f := by
    simp only [Equiv.symm_apply_apply, Category.id_comp, Equiv.apply_symm_apply]
  comp_id {x y} f := by
    simp only [Equiv.symm_apply_apply, Category.comp_id, Equiv.apply_symm_apply]
  assoc {w x y z} f g h := by
    simp only [Equiv.symm_apply_apply, Category.assoc]

@[simp] theorem hC_id_mk (C : SimplicialCat.{o, v}) (x : hC C) :
    (𝟙 x) = SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) := rfl

@[simp] theorem hC_comp_mk (C : SimplicialCat.{o, v}) {x y z : hC C}
    (f : (C.enriched.Hom x y) _⦋0⦌) (g : (C.enriched.Hom y z) _⦋0⦌) :
    (@CategoryStruct.comp (hC C) (hC_category C).toCategoryStruct x y z
      (SSet.π₀.mk f) (SSet.π₀.mk g)) =
      SSet.π₀.mk ((C.enriched.comp x y z).app (op ⦋0⦌) (f, g)) := rfl

/-- Every original ordinary enriched functor acts on every literal pi0 Hom component. -/
def hFunctor {C : SimplicialCat.{o, v}} {D : SimplicialCat.{o₂, v}}
    (F : EnrichedFunctor SSet.{v} C.Obj D.Obj) : hC C ⥤ hC D where
  obj := F.obj
  map {x y} := SSet.mapπ₀ (F.map x y)
  map_id x := congrArg SSet.π₀.mk
    (congrFun (NatTrans.congr_app (F.map_id x) (op ⦋0⦌)) PUnit.unit)
  map_comp {x y z} f g := by
    obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective f
    obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective g
    exact congrArg SSet.π₀.mk
      (congrFun (NatTrans.congr_app (F.map_comp x y z) (op ⦋0⦌)) (f, g))

@[simp] theorem hFunctor_id (C : SimplicialCat.{o, v}) :
    hFunctor (EnrichedFunctor.id SSet C.Obj) = 𝟭 (hC C) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro x; rfl
  case h_map =>
    intro x y f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      SSet.mapπ₀_id_apply f

@[simp] theorem hFunctor_comp {C : SimplicialCat.{o, v}}
    {D : SimplicialCat.{o₂, v}} {E : SimplicialCat.{o₃, v}}
    (f : EnrichedFunctor SSet.{v} C.Obj D.Obj)
    (g : EnrichedFunctor SSet.{v} D.Obj E.Obj) :
    hFunctor (EnrichedFunctor.comp SSet f g) = hFunctor f ⋙ hFunctor g := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro x; rfl
  case h_map =>
    intro x y z
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      SSet.mapπ₀_comp_apply (f.map x y) (g.map (f.obj x) (f.obj y)) z

end DaggerOrdinaryPiZeroCategory
