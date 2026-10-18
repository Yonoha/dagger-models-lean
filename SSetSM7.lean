import TopCatModelCategory.SSet.Fibrations
import IinjBridge

/-! Exact ordinary simplicial-set corner maps for the fixed-category SM7 proof. -/

open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Limits
open scoped SSet.modelCategoryQuillen

universe u

set_option autoImplicit false

namespace DaggerSSetSM7

variable {A B K L X Y : SSet.{u}}

/-- The existing generic pushout data on the literal chosen simplicial-set pushout. -/
noncomputable def pushoutTensor (i : A ⟶ B) (f : K ⟶ L) : SSet.PushoutTensor i f :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

theorem pushoutTensor_ι (i : A ⟶ B) (f : K ⟶ L) :
    (pushoutTensor i f).ι = SSet.fromPushoutProduct i f := by
  apply pushout.hom_ext
  · simpa [pushoutTensor] using Functor.PushoutObjObj.inl_ι (pushoutTensor i f)
  · simpa [pushoutTensor] using Functor.PushoutObjObj.inr_ι (pushoutTensor i f)

/-- Both original arrows are retained in the comparison with their image inclusions. -/
noncomputable def pushoutProductImageIso (i : A ⟶ B) (f : K ⟶ L) [Mono i] [Mono f] :
    Arrow.mk (SSet.fromPushoutProduct i f) ≅
      Arrow.mk ((SSet.Subcomplex.range i).unionProd (SSet.Subcomplex.range f)).ι :=
  SSet.fromPushoutProductCongr
    (Arrow.isoMk (asIso (SSet.Subcomplex.toRange f)) (Iso.refl _) (by simp))
    (Arrow.isoMk (asIso (SSet.Subcomplex.toRange i)) (Iso.refl _) (by simp)) ≪≫
      SSet.fromPushoutProductιιIso _ _

theorem pushoutProduct_mono (i : A ⟶ B) (f : K ⟶ L) [Mono i] [Mono f] :
    Mono (SSet.fromPushoutProduct i f) :=
  ((MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff
    (pushoutProductImageIso i f)).2 (by change Mono _; infer_instance)

theorem pushoutProduct_anodyne_left (i : A ⟶ B) (f : K ⟶ L) [Mono f]
    (hi : SSet.anodyneExtensions i) : SSet.anodyneExtensions (SSet.fromPushoutProduct i f) := by
  rw [← pushoutTensor_ι]
  exact SSet.anodyneExtensions.pushoutTensorι₁ (pushoutTensor i f) hi

theorem corner_fibration (i : A ⟶ B) (p : X ⟶ Y) [Mono i] [Fibration p] :
    Fibration (SSet.ihomToPullback i p) := inferInstance

/-- An anodyne left input makes the same full corner a trivial fibration. -/
theorem corner_trivial_of_anodyne (i : A ⟶ B) (p : X ⟶ Y)
    (hi : SSet.anodyneExtensions i) [Fibration p] :
    Fibration (SSet.ihomToPullback i p) ∧ WeakEquivalence (SSet.ihomToPullback i p) := by
  apply (DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial _).1
  intro n
  rw [SSet.hasLiftingProperty_iHomToPullback_iff]
  exact (pushoutProduct_anodyne_left i (SSet.boundary n).ι hi).hasLeftLiftingProperty p

/-- A trivial right input gives boundary lifting in every dimension, including zero. -/
theorem corner_trivial_of_trivial (i : A ⟶ B) (p : X ⟶ Y)
    [Mono i] [Fibration p] [WeakEquivalence p] :
    Fibration (SSet.ihomToPullback i p) ∧ WeakEquivalence (SSet.ihomToPullback i p) := by
  apply (DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial _).1
  intro n
  rw [SSet.hasLiftingProperty_iHomToPullback_iff]
  letI := pushoutProduct_mono i (SSet.boundary n).ι
  infer_instance

/-- The corner's weak equivalence has the original realization/singular meaning. -/
theorem corner_geometric (i : A ⟶ B) (p : X ⟶ Y) [Mono i] [Fibration p]
    (h : SSet.anodyneExtensions i ∨ WeakEquivalence p) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (SSet.ihomToPullback i p))) := by
  apply (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).1
  rcases h with hi | hp
  · exact (corner_trivial_of_anodyne i p hi).2
  · letI := hp
    exact (corner_trivial_of_trivial i p).2

/-- SM7 for the literal simplicial-set cotensor corner, including both weak-input cases. -/
theorem corner_sm7 (i : A ⟶ B) (p : X ⟶ Y) [Mono i] [Fibration p] :
    Fibration (SSet.ihomToPullback i p) ∧
      ((WeakEquivalence i ∨ WeakEquivalence p) →
        WeakEquivalence (SSet.ihomToPullback i p)) := by
  refine ⟨corner_fibration i p, ?_⟩
  rintro (hi | hp)
  · letI := hi
    letI : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
    have ha : SSet.anodyneExtensions i := by
      change (fibrations SSet.{u}).llp i
      rw [fibrations_llp]
      exact mem_trivialCofibrations i
    exact (corner_trivial_of_anodyne i p ha).2
  · letI := hp
    exact (corner_trivial_of_trivial i p).2

end DaggerSSetSM7
