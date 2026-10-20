import DaggerModels.FreeCofibration
import DaggerModels.FreeDaggerPushout

/-!
# Free dagger completion sends monomorphisms to free cofibrations

This proves Part I `dj.cor.Fdag-free` for the actual free functor and every simplicial
monomorphism, in every universe. The proof uses the actual degreewise pushout, its
coprojections and their intersection over the totally degenerate vertex simplices.
-/

open CategoryTheory CategoryTheory.Limits Functor Opposite Simplicial

universe u

namespace DaggerModels
namespace FreeDaggerPushout

/-- Evaluation gives the actual pushout of simplex types in each degree. -/
theorem pushoutAt (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    IsPushout ((SSetVertices.inclusion A).app n) ((SSetVertices.opInclusion A).app n)
      ((inl A).app n) ((inr A).app n) :=
  (IsPushout.of_hasPushout (SSetVertices.inclusion A) (SSetVertices.opInclusion A)).map
    ((evaluation _ (Type u)).obj n)

theorem vertex_inclusion_injective (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((SSetVertices.inclusion A).app n) :=
  (mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app (SSetVertices.inclusion A)).1
      (SSetVertices.mono_inclusion A) n)

theorem vertex_opInclusion_injective (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((SSetVertices.opInclusion A).app n) := by
  change Function.Injective ((SSetVertices.inclusion A).app n)
  exact vertex_inclusion_injective A n

theorem inl_app_injective (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((inl A).app n) :=
  Types.pushoutCocone_inr_injective_of_isColimit (pushoutAt A n).flip.isColimit
    (vertex_opInclusion_injective A n)

theorem inr_app_injective (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((inr A).app n) :=
  Types.pushoutCocone_inr_injective_of_isColimit (pushoutAt A n).isColimit
    (vertex_inclusion_injective A n)

/-- Two different-copy representatives agree precisely on their shared vertex image. -/
theorem inl_eq_inr_iff (A : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (a : A.obj n) (b : A.op.obj n) :
    (inl A).app n a = (inr A).app n b ↔
      ∃ v : A.obj (op ⦋0⦌), (SSetVertices.inclusion A).app n v = a ∧
        (SSetVertices.opInclusion A).app n v = b :=
  Types.pushoutCocone_inl_eq_inr_iff_of_isColimit (pushoutAt A n).isColimit
    (vertex_inclusion_injective A n) a b

/-- Every simplex in the pushout has a representative in one of the two copies. -/
theorem exists_copy (A : SSet.{u}) (n : SimplexCategoryᵒᵖ) (x : (underlying A).obj n) :
    (∃ a : A.obj n, (inl A).app n a = x) ∨ ∃ b : A.op.obj n, (inr A).app n b = x :=
  Types.eq_or_eq_of_isPushout (pushoutAt A n) x

@[simp] theorem daggerSimplex_inl (A : SSet.{u}) (n : ℕ) (a : A _⦋n⦌) :
    (obj A).daggerSimplex ((inl A).app (op ⦋n⦌) a) =
      (inr A).app (op ⦋n⦌) (SSet.opObjEquiv.symm a) :=
  congrFun (NatTrans.congr_app (inl_daggerMap A) (op ⦋n⦌)) a

@[simp] theorem daggerSimplex_inr (A : SSet.{u}) (n : ℕ) (b : A.op _⦋n⦌) :
    (obj A).daggerSimplex ((inr A).app (op ⦋n⦌) b) =
      (inl A).app (op ⦋n⦌) (SSet.opObjEquiv b) :=
  congrFun (NatTrans.congr_app (inr_daggerMap A) (op ⦋n⦌)) b

/-- All positive-dimensional simplices of the vertex simplicial set are degenerate. -/
theorem vertex_mem_degenerate (A : SSet.{u}) (n : ℕ) (hn : 0 < n)
    (v : A.obj (op ⦋0⦌)) : v ∈ (SSetVertices.obj A).degenerate n :=
  ⟨0, hn, SimplexCategory.const ⦋n⦌ ⦋0⦌ 0, v, rfl⟩

/-- The actual swap is free on every nondegenerate positive-dimensional simplex. -/
theorem nonDegenerate_not_fixed (A : SSet.{u}) (n : ℕ) (hn : 0 < n)
    (x : (underlying A) _⦋n⦌) (hx : x ∈ (underlying A).nonDegenerate n) :
    (obj A).daggerSimplex x ≠ x := by
  intro hfix
  obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) := exists_copy A (op ⦋n⦌) x
  · rw [daggerSimplex_inl] at hfix
    obtain ⟨v, ha, _⟩ := (inl_eq_inr_iff A (op ⦋n⦌) a _).1 hfix.symm
    apply hx
    rw [← ha]
    exact SSet.degenerate_app_apply (vertex_mem_degenerate A n hn v)
      (SSetVertices.inclusion A ≫ inl A)
  · rw [daggerSimplex_inr] at hfix
    obtain ⟨v, _, hb⟩ := (inl_eq_inr_iff A (op ⦋n⦌) _ b).1 hfix
    apply hx
    rw [← hb]
    exact SSet.degenerate_app_apply (vertex_mem_degenerate A n hn v)
      (SSetVertices.opInclusion A ≫ inr A)

/-- A monomorphism reflects the image of the totally degenerate vertex simplices. -/
theorem exists_vertex_of_image {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (n : SimplexCategoryᵒᵖ) (a : A.obj n) (v : B.obj (op ⦋0⦌))
    (hv : (SSetVertices.inclusion B).app n v = f.app n a) :
    ∃ w : A.obj (op ⦋0⦌), (SSetVertices.inclusion A).app n w = a ∧
      f.app (op ⦋0⦌) w = v := by
  let q := (SimplexCategory.const ⦋0⦌ n.unop 0).op
  let w := A.map q a
  have hfv : f.app (op ⦋0⦌) w = v := by
    calc
      f.app (op ⦋0⦌) w = B.map q (f.app n a) := congrFun (f.naturality q) a
      _ = B.map q ((SSetVertices.inclusion B).app n v) := congrArg (B.map q) hv.symm
      _ = v := by
        change B.map (SimplexCategory.const ⦋0⦌ n.unop 0).op
          (B.map (SimplexCategory.const n.unop ⦋0⦌ 0).op v) = v
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp, SimplexCategory.const_comp,
          SimplexCategory.const_apply, SimplexCategory.const_eq_id, op_id, B.map_id]
        rfl
  refine ⟨w, ?_, hfv⟩
  apply (mono_iff_injective (f.app n)).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance n)
  calc
    f.app n ((SSetVertices.inclusion A).app n w) =
        (SSetVertices.inclusion B).app n (f.app (op ⦋0⦌) w) :=
      (congrFun (NatTrans.congr_app (SSetVertices.map_inclusion f) n) w).symm
    _ = (SSetVertices.inclusion B).app n v := congrArg _ hfv
    _ = f.app n a := hv

theorem inl_eq_inr_of_image {A B : SSet.{u}} (f : A ⟶ B) [Mono f]
    (n : SimplexCategoryᵒᵖ) (a : A.obj n) (b : A.op.obj n)
    (h : (inl B).app n (f.app n a) =
      (inr B).app n ((SSet.opFunctor.map f).app n b)) :
    (inl A).app n a = (inr A).app n b := by
  obtain ⟨v, ha, hb⟩ := (inl_eq_inr_iff B n _ _).1 h
  obtain ⟨w, hw, _⟩ := exists_vertex_of_image f n a v ha
  refine (inl_eq_inr_iff A n a b).2 ⟨w, hw, ?_⟩
  change (SSetVertices.inclusion A).app n w = SSet.opObjEquiv b
  apply (mono_iff_injective (f.app n)).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance n)
  change (SSetVertices.inclusion B).app n v = f.app n (SSet.opObjEquiv b) at hb
  exact congrArg (f.app n) hw |>.trans (ha.symm.trans hb)

@[simp] theorem mapUnderlying_inl_apply {A B : SSet.{u}} (f : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (a : A.obj n) :
    (mapUnderlying f).app n ((inl A).app n a) = (inl B).app n (f.app n a) :=
  congrFun (NatTrans.congr_app (inl_mapUnderlying f) n) a

@[simp] theorem mapUnderlying_inr_apply {A B : SSet.{u}} (f : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (b : A.op.obj n) :
    (mapUnderlying f).app n ((inr A).app n b) =
      (inr B).app n ((SSet.opFunctor.map f).app n b) :=
  congrFun (NatTrans.congr_app (inr_mapUnderlying f) n) b

/-- A monomorphism remains a monomorphism under the actual two-copy pushout map. -/
theorem mapUnderlying_mono {A B : SSet.{u}} (f : A ⟶ B) [Mono f] :
    Mono (mapUnderlying f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  have hf : Function.Injective (f.app n) :=
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance n)
  intro x y h
  obtain (⟨a, rfl⟩ | ⟨b, rfl⟩) := exists_copy A n x
  · obtain (⟨a', rfl⟩ | ⟨b', rfl⟩) := exists_copy A n y
    · rw [mapUnderlying_inl_apply, mapUnderlying_inl_apply] at h
      exact congrArg ((inl A).app n) (hf (inl_app_injective B n h))
    · rw [mapUnderlying_inl_apply, mapUnderlying_inr_apply] at h
      exact inl_eq_inr_of_image f n a b' h
  · obtain (⟨a', rfl⟩ | ⟨b', rfl⟩) := exists_copy A n y
    · rw [mapUnderlying_inr_apply, mapUnderlying_inl_apply] at h
      exact (inl_eq_inr_of_image f n a' b h.symm).symm
    · rw [mapUnderlying_inr_apply, mapUnderlying_inr_apply] at h
      apply congrArg ((inr A).app n)
      apply hf
      exact inr_app_injective B n h

instance preservesMonomorphisms : functor.{u}.PreservesMonomorphisms where
  preserves f := (DaggerSSet.mono_iff_mono_hom (functor.map f)).2
    (mapUnderlying_mono f)

end FreeDaggerPushout

/-- Every free dagger completion has a free swap on all positive nondegenerate simplices. -/
theorem freeDagger_nonDegenerate_not_fixed
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    (A : SSet.{u}) (n : ℕ) (hn : 0 < n)
    (x : (F.obj A).toSSet _⦋n⦌) (hx : x ∈ (F.obj A).toSSet.nonDegenerate n) :
    (F.obj A).daggerSimplex x ≠ x := by
  let e := Adjunction.leftAdjointUniq adj FreeDaggerPushout.adjunction
  let g : F.obj A ⟶ FreeDaggerPushout.obj A := e.hom.app A
  have : IsIso g.hom := by
    change IsIso (DaggerSSet.forget.map g)
    infer_instance
  have hy : g.hom.app (op ⦋n⦌) x ∈ (FreeDaggerPushout.underlying A).nonDegenerate n :=
    (SSet.nonDegenerate_iff_of_isIso g.hom x).2 hx
  intro hfix
  apply FreeDaggerPushout.nonDegenerate_not_fixed A n hn _ hy
  exact (g.dagger_comm x).symm.trans (congrArg (g.hom.app (op ⦋n⦌)) hfix)

/-- For any actual free–forgetful adjunction, simplicial monomorphisms become free
cofibrations, as in Part I `dj.cor.Fdag-free`. -/
theorem freeDagger_map_freeCofibration
    (F : SSet.{u} ⥤ DaggerSSet.{u}) (adj : F ⊣ DaggerSSet.forget)
    {K L : SSet.{u}} (i : K ⟶ L) [Mono i] : DaggerSSet.FreeCofibration (F.map i) := by
  let e := Adjunction.leftAdjointUniq FreeDaggerPushout.adjunction adj
  let : F.PreservesMonomorphisms := Functor.preservesMonomorphisms.of_iso e
  refine ⟨inferInstance, ?_⟩
  intro n hn x hx _hnew
  exact freeDagger_nonDegenerate_not_fixed F adj L n hn x hx

/-- The canonical free dagger functor sends every simplicial monomorphism to a free
cofibration. -/
theorem freeDagger_map_isFreeCofibration {K L : SSet.{u}} (i : K ⟶ L) [Mono i] :
    DaggerSSet.FreeCofibration (freeDagger.map i) :=
  freeDagger_map_freeCofibration freeDagger freeDaggerAdjunction i

end DaggerModels
