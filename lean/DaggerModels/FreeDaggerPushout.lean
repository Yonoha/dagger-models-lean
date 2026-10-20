import DaggerModels.FreeDagger
import DaggerModels.Vertices
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The pushout presentation of free dagger completion

This file identifies the free dagger functor from `dj.not.adjunctions` with the
pushout of a simplicial set and its reversal over its discrete vertices.
-/

open CategoryTheory CategoryTheory.Limits Functor Opposite Simplicial

universe u

namespace DaggerModels

namespace DaggerSSet

/-- The chosen dagger is an isomorphism, with inverse given by the reversed dagger. -/
def daggerIso (Y : DaggerSSet.{u}) : Y.toSSet ≅ Y.toSSet.op where
  hom := Y.dagger
  inv := SSet.opFunctor.map Y.dagger ≫ SSet.opFunctorCompOpFunctorIso.hom.app Y.toSSet
  hom_inv_id := by
    ext n x
    exact Y.involutive n.unop.len x
  inv_hom_id := by
    ext n x
    exact Y.involutive n.unop.len x

/-- Reversing the inverse dagger recovers the dagger after the double-reversal unit. -/
theorem daggerIso_inv_op (Y : DaggerSSet.{u}) :
    SSet.opFunctorCompOpFunctorIso.inv.app Y.toSSet ≫
      SSet.opFunctor.map Y.daggerIso.inv = Y.dagger := by
  ext n x
  rfl

end DaggerSSet

namespace FreeDaggerPushout

/-- The underlying pushout of the two copies over the discrete vertices. -/
noncomputable def underlying (A : SSet.{u}) : SSet.{u} :=
  pushout (SSetVertices.inclusion A) (SSetVertices.opInclusion A)

noncomputable def inl (A : SSet.{u}) : A ⟶ underlying A :=
  pushout.inl _ _

noncomputable def inr (A : SSet.{u}) : A.op ⟶ underlying A :=
  pushout.inr _ _

/-- The swap involution, reversing both copies of the simplicial set. -/
noncomputable def daggerMap (A : SSet.{u}) : underlying A ⟶ (underlying A).op :=
  pushout.desc (SSet.opFunctorCompOpFunctorIso.inv.app A ≫ SSet.opFunctor.map (inr A))
    (SSet.opFunctor.map (inl A)) (by
      rw [← Category.assoc, ← SSetVertices.opIso_hom_op_opInclusion,
        Category.assoc, ← SSet.opFunctor.map_comp]
      change (SSetVertices.opIso A).hom ≫
        SSet.opFunctor.map (SSetVertices.opInclusion A ≫ pushout.inr _ _) = _
      rw [← pushout.condition, SSet.opFunctor.map_comp, ← Category.assoc,
        SSetVertices.opIso_hom_op_inclusion]
      rfl)

@[simp] theorem inl_daggerMap (A : SSet.{u}) :
    inl A ≫ daggerMap A =
      SSet.opFunctorCompOpFunctorIso.inv.app A ≫ SSet.opFunctor.map (inr A) := by
  simp [inl, daggerMap]

@[simp] theorem inr_daggerMap (A : SSet.{u}) :
    inr A ≫ daggerMap A = SSet.opFunctor.map (inl A) := by
  simp [inr, daggerMap]

/-- The categorical double-swap equation, including the double-reversal identification. -/
theorem daggerMap_involutive (A : SSet.{u}) :
    daggerMap A ≫ SSet.opFunctor.map (daggerMap A) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app (underlying A) = 𝟙 _ := by
  have hL := SSet.opFunctorCompOpFunctorIso.hom.naturality (inl A)
  change SSet.opFunctor.map (SSet.opFunctor.map (inl A)) ≫
    SSet.opFunctorCompOpFunctorIso.hom.app (underlying A) =
    SSet.opFunctorCompOpFunctorIso.hom.app A ≫ inl A at hL
  have hR := SSet.opFunctorCompOpFunctorIso.hom.naturality (inr A)
  change SSet.opFunctor.map (SSet.opFunctor.map (inr A)) ≫
    SSet.opFunctorCompOpFunctorIso.hom.app (underlying A) =
    SSet.opFunctorCompOpFunctorIso.hom.app A.op ≫ inr A at hR
  have hε := SSet.opEquivalence.functor_unitIso_comp A
  change SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.inv.app A) ≫
    SSet.opFunctorCompOpFunctorIso.hom.app A.op = 𝟙 _ at hε
  apply pushout.hom_ext
  · change inl A ≫ _ = inl A ≫ _
    simp only [← Category.assoc, inl_daggerMap, Category.comp_id]
    simp only [Category.assoc, ← SSet.opFunctor.map_comp_assoc, inr_daggerMap, hL]
    simp
  · change inr A ≫ _ = inr A ≫ _
    simp only [← Category.assoc, inr_daggerMap, Category.comp_id]
    rw [← SSet.opFunctor.map_comp, inl_daggerMap, SSet.opFunctor.map_comp]
    simp only [Category.assoc]
    rw [hR, ← Category.assoc, hε]
    simp

/-- Every vertex comes from the first copy, because the evaluated seam maps are identities. -/
instance inl_app_zero_isIso (A : SSet.{u}) : IsIso ((inl A).app (op ⦋0⦌)) := by
  haveI : IsIso (((evaluation _ (Type u)).obj (op ⦋0⦌)).map
      (SSetVertices.opInclusion A)) := by
    change IsIso ((SSetVertices.opInclusion A).app (op ⦋0⦌))
    infer_instance
  have h := (IsPushout.of_hasPushout (SSetVertices.inclusion A)
    (SSetVertices.opInclusion A)).map ((evaluation _ (Type u)).obj (op ⦋0⦌))
  exact h.isIso_inl_of_isIso

/-- The swap fixes all vertices, not just the image of a selected vertex map. -/
theorem daggerMap_fixedVertices (A : SSet.{u}) (x : (underlying A).obj (op ⦋0⦌)) :
    SSet.opObjEquiv ((daggerMap A).app (op ⦋0⦌) x) = x := by
  have hd := NatTrans.congr_app (inl_daggerMap A) (op ⦋0⦌)
  have hc := NatTrans.congr_app (pushout.condition
    (f := SSetVertices.inclusion A) (g := SSetVertices.opInclusion A)) (op ⦋0⦌)
  have hδ : (daggerMap A).app (op ⦋0⦌) = 𝟙 ((underlying A).obj (op ⦋0⦌)) := by
    apply (cancel_epi ((inl A).app (op ⦋0⦌))).1
    ext a
    have hd' := congrFun hd a
    have hc' := congrFun hc a
    change SSet.opObjEquiv ((daggerMap A).app (op ⦋0⦌) ((inl A).app (op ⦋0⦌) a)) =
      (inr A).app (op ⦋0⦌) a at hd'
    have hc'' : (inl A).app (op ⦋0⦌) a = (inr A).app (op ⦋0⦌) a := by
      simpa [NatTrans.comp_app, SSetVertices.inclusion_app_zero_eq_id,
        SSetVertices.opInclusion_app_zero_eq_id, inl, inr] using hc'
    exact hd'.trans hc''.symm
  exact congrFun hδ x

/-- The pushout with its actual swap dagger is a dagger simplicial set. -/
noncomputable def obj (A : SSet.{u}) : DaggerSSet.{u} where
  toSSet := underlying A
  dagger := daggerMap A
  involutive n x := congrFun (NatTrans.congr_app (daggerMap_involutive A) (op ⦋n⦌)) x
  fixedVertices := daggerMap_fixedVertices A

/-- The map of pushouts induced by a simplicial map and its reversal. -/
noncomputable def mapUnderlying {A B : SSet.{u}} (f : A ⟶ B) : underlying A ⟶ underlying B :=
  pushout.map _ _ _ _ f (SSet.opFunctor.map f) (SSetVertices.map f)
    (SSetVertices.map_inclusion f).symm (SSetVertices.map_opInclusion f).symm

@[simp] theorem inl_mapUnderlying {A B : SSet.{u}} (f : A ⟶ B) :
    inl A ≫ mapUnderlying f = f ≫ inl B := by
  simp [inl, mapUnderlying]

@[simp] theorem inr_mapUnderlying {A B : SSet.{u}} (f : A ⟶ B) :
    inr A ≫ mapUnderlying f = SSet.opFunctor.map f ≫ inr B := by
  simp [inr, mapUnderlying]

/-- The induced pushout map preserves the actual swap dagger. -/
theorem mapUnderlying_comm {A B : SSet.{u}} (f : A ⟶ B) :
    mapUnderlying f ≫ daggerMap B = daggerMap A ≫ SSet.opFunctor.map (mapUnderlying f) := by
  have hε := SSet.opFunctorCompOpFunctorIso.inv.naturality f
  change f ≫ SSet.opFunctorCompOpFunctorIso.inv.app B =
    SSet.opFunctorCompOpFunctorIso.inv.app A ≫ SSet.opFunctor.map (SSet.opFunctor.map f) at hε
  apply pushout.hom_ext
  · change inl A ≫ _ = inl A ≫ _
    simp only [← Category.assoc, inl_mapUnderlying, inl_daggerMap]
    simp only [Category.assoc, inl_daggerMap]
    rw [← SSet.opFunctor.map_comp, inr_mapUnderlying, SSet.opFunctor.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ SSet.opFunctor.map (inr B)) hε
  · change inr A ≫ _ = inr A ≫ _
    simp only [← Category.assoc, inr_mapUnderlying, inr_daggerMap]
    simp only [Category.assoc, inr_daggerMap]
    simpa only [SSet.opFunctor.map_comp] using
      (congrArg (fun k ↦ SSet.opFunctor.map k) (inl_mapUnderlying f)).symm

/-- The induced map as a morphism of dagger simplicial sets. -/
noncomputable def map {A B : SSet.{u}} (f : A ⟶ B) : obj A ⟶ obj B where
  hom := mapUnderlying f
  comm := mapUnderlying_comm f

/-- The explicit pushout construction is a functor. -/
noncomputable def functor : SSet.{u} ⥤ DaggerSSet.{u} where
  obj := obj
  map := map
  map_id A := by
    apply DaggerSSet.Hom.ext
    change mapUnderlying (𝟙 A) = 𝟙 (underlying A)
    apply pushout.hom_ext
    · change inl A ≫ mapUnderlying (𝟙 A) = inl A ≫ 𝟙 _
      simp only [inl_mapUnderlying, Category.id_comp, Category.comp_id]
    · change inr A ≫ mapUnderlying (𝟙 A) = inr A ≫ 𝟙 _
      simp only [inr_mapUnderlying, SSet.opFunctor.map_id, Category.id_comp, Category.comp_id]
  map_comp {A B C} f g := by
    apply DaggerSSet.Hom.ext
    change mapUnderlying (f ≫ g) = mapUnderlying f ≫ mapUnderlying g
    apply pushout.hom_ext
    · change inl A ≫ mapUnderlying (f ≫ g) = inl A ≫ (mapUnderlying f ≫ mapUnderlying g)
      simp only [← Category.assoc, inl_mapUnderlying]
      simp only [Category.assoc, inl_mapUnderlying]
    · change inr A ≫ mapUnderlying (f ≫ g) = inr A ≫ (mapUnderlying f ≫ mapUnderlying g)
      simp only [← Category.assoc, inr_mapUnderlying]
      simp only [Category.assoc, inr_mapUnderlying, SSet.opFunctor.map_comp]

/-- Maps on the two copies agree on the vertex simplicial set, because daggers fix
the totally degenerate simplices. -/
theorem desc_agreement {A : SSet.{u}} {Y : DaggerSSet.{u}} (f : A ⟶ Y.toSSet) :
    SSetVertices.inclusion A ≫ f =
      SSetVertices.opInclusion A ≫ SSet.opFunctor.map f ≫ Y.daggerIso.inv := by
  ext n x
  change f.app n (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x) =
    Y.daggerSimplex (n := n.unop.len)
      (f.app n (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x))
  have hn := congrFun (f.naturality (SimplexCategory.const n.unop ⦋0⦌ 0).op) x
  change f.app n (A.map (SimplexCategory.const n.unop ⦋0⦌ 0).op x) =
    Y.toSSet.map (SimplexCategory.const n.unop ⦋0⦌ 0).op (f.app (op ⦋0⦌) x) at hn
  rw [hn]
  exact (Y.dagger_constant (m := n.unop.len) (n := 0) 0 (f.app (op ⦋0⦌) x)).symm

/-- Extend a simplicial map by its forced value on the reversed copy. -/
noncomputable def descUnderlying {A : SSet.{u}} {Y : DaggerSSet.{u}}
    (f : A ⟶ Y.toSSet) : underlying A ⟶ Y.toSSet :=
  pushout.desc f (SSet.opFunctor.map f ≫ Y.daggerIso.inv) (desc_agreement f)

@[simp] theorem inl_descUnderlying {A : SSet.{u}} {Y : DaggerSSet.{u}}
    (f : A ⟶ Y.toSSet) : inl A ≫ descUnderlying f = f := by
  simp [inl, descUnderlying]

@[simp] theorem inr_descUnderlying {A : SSet.{u}} {Y : DaggerSSet.{u}}
    (f : A ⟶ Y.toSSet) :
    inr A ≫ descUnderlying f = SSet.opFunctor.map f ≫ Y.daggerIso.inv := by
  simp [inr, descUnderlying]

/-- The extension commutes with the swap dagger. -/
theorem descUnderlying_comm {A : SSet.{u}} {Y : DaggerSSet.{u}} (f : A ⟶ Y.toSSet) :
    descUnderlying f ≫ Y.dagger = daggerMap A ≫ SSet.opFunctor.map (descUnderlying f) := by
  have hε := SSet.opFunctorCompOpFunctorIso.inv.naturality f
  change f ≫ SSet.opFunctorCompOpFunctorIso.inv.app Y.toSSet =
    SSet.opFunctorCompOpFunctorIso.inv.app A ≫ SSet.opFunctor.map (SSet.opFunctor.map f) at hε
  have hi := Y.daggerIso.inv_hom_id
  change Y.daggerIso.inv ≫ Y.dagger = 𝟙 _ at hi
  apply pushout.hom_ext
  · change inl A ≫ _ = inl A ≫ _
    simp only [← Category.assoc, inl_descUnderlying, inl_daggerMap]
    simp only [Category.assoc]
    rw [← SSet.opFunctor.map_comp, inr_descUnderlying, SSet.opFunctor.map_comp]
    rw [← Category.assoc, ← hε, Category.assoc, Y.daggerIso_inv_op]
  · change inr A ≫ _ = inr A ≫ _
    simp only [← Category.assoc, inr_descUnderlying, inr_daggerMap]
    simp only [Category.assoc, hi, Category.comp_id]
    rw [← SSet.opFunctor.map_comp, inl_descUnderlying]

/-- The universal extension as a dagger-compatible map. -/
noncomputable def desc {A : SSet.{u}} {Y : DaggerSSet.{u}} (f : A ⟶ Y.toSSet) : obj A ⟶ Y where
  hom := descUnderlying f
  comm := descUnderlying_comm f

/-- Dagger compatibility forces the restriction to the second copy. -/
theorem inr_hom {A : SSet.{u}} {Y : DaggerSSet.{u}} (g : obj A ⟶ Y) :
    inr A ≫ g.hom = SSet.opFunctor.map (inl A ≫ g.hom) ≫ Y.daggerIso.inv := by
  apply Y.daggerIso.eq_comp_inv.2
  change (inr A ≫ g.hom) ≫ Y.dagger = SSet.opFunctor.map (inl A ≫ g.hom)
  rw [Category.assoc, g.comm, ← Category.assoc]
  change (inr A ≫ daggerMap A) ≫ SSet.opFunctor.map g.hom =
    SSet.opFunctor.map (inl A ≫ g.hom)
  rw [inr_daggerMap, ← SSet.opFunctor.map_comp]

/-- Restriction to the first copy is the free--forgetful hom-set equivalence. -/
noncomputable def homEquiv (A : SSet.{u}) (Y : DaggerSSet.{u}) :
    (obj A ⟶ Y) ≃ (A ⟶ Y.toSSet) where
  toFun g := inl A ≫ g.hom
  invFun := desc
  left_inv g := by
    apply DaggerSSet.Hom.ext
    change descUnderlying (inl A ≫ g.hom) = g.hom
    apply pushout.hom_ext
    · change inl A ≫ descUnderlying (inl A ≫ g.hom) = inl A ≫ g.hom
      exact inl_descUnderlying _
    · change inr A ≫ descUnderlying (inl A ≫ g.hom) = inr A ≫ g.hom
      rw [inr_descUnderlying]
      exact (inr_hom g).symm
  right_inv f := inl_descUnderlying f

/-- The explicit pushout construction is left adjoint to the original forgetful functor. -/
noncomputable def adjunction : functor.{u} ⊣ DaggerSSet.forget.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun {A B Y} f g ↦ by
        apply (homEquiv A Y).injective
        change inl A ≫ descUnderlying (f ≫ g) =
          inl A ≫ (mapUnderlying f ≫ descUnderlying g)
        simp only [← Category.assoc, inl_descUnderlying, inl_mapUnderlying]
        simp only [Category.assoc, inl_descUnderlying]
      homEquiv_naturality_right := fun {A Y Z} g h ↦ by
        change inl A ≫ (g.hom ≫ h.hom) = (inl A ≫ g.hom) ≫ h.hom
        exact (Category.assoc _ _ _).symm }

@[simp] theorem adjunction_unit_app (A : SSet.{u}) : adjunction.unit.app A = inl A := rfl

/-- The concrete pushout free functor and the Kan-extension free functor agree naturally. -/
noncomputable def isoFreeDagger : functor.{u} ≅ freeDagger.{u} :=
  Adjunction.leftAdjointUniq adjunction freeDaggerAdjunction

/-- The comparison identifies the first pushout inclusion with the original free unit. -/
theorem inl_isoFreeDagger_hom (A : SSet.{u}) :
    inl A ≫ DaggerSSet.forget.map (isoFreeDagger.hom.app A) = freeDaggerAdjunction.unit.app A :=
  Adjunction.unit_leftAdjointUniq_hom_app adjunction freeDaggerAdjunction A

/-- The second-copy inclusions form a natural transformation. -/
noncomputable def rightInclusion : SSet.opFunctor ⟶ functor.{u} ⋙ DaggerSSet.forget where
  app := inr
  naturality {_ _} f := (inr_mapUnderlying f).symm

end FreeDaggerPushout

/-- Every free dagger adjunction has the concrete pushout presentation, with its specified
unit as first inclusion and a natural second inclusion satisfying the two swap equations. -/
theorem freeDagger_pushout (F : SSet.{u} ⥤ DaggerSSet.{u})
    (adj : F ⊣ DaggerSSet.forget.{u}) :
    ∃ r : SSet.opFunctor ⟶ F ⋙ DaggerSSet.forget, ∀ A,
      IsPushout (SSetVertices.inclusion A) (SSetVertices.opInclusion A)
        (adj.unit.app A) (r.app A) ∧
      (adj.unit.app A ≫ (F.obj A).dagger =
        (SSet.opFunctorCompOpFunctorIso.app A).inv ≫ SSet.opFunctor.map (r.app A)) ∧
      (r.app A ≫ (F.obj A).dagger = SSet.opFunctor.map (adj.unit.app A)) := by
  let e := Adjunction.leftAdjointUniq FreeDaggerPushout.adjunction adj
  let r := FreeDaggerPushout.rightInclusion ≫ whiskerRight e.hom DaggerSSet.forget
  refine ⟨r, fun A ↦ ?_⟩
  have hu : FreeDaggerPushout.inl A ≫ (e.hom.app A).hom = adj.unit.app A :=
    Adjunction.unit_leftAdjointUniq_hom_app FreeDaggerPushout.adjunction adj A
  have he := (e.hom.app A).comm
  change (e.hom.app A).hom ≫ (F.obj A).dagger =
    FreeDaggerPushout.daggerMap A ≫ SSet.opFunctor.map (e.hom.app A).hom at he
  refine ⟨?_, ?_, ?_⟩
  · apply (IsPushout.of_hasPushout (SSetVertices.inclusion A)
      (SSetVertices.opInclusion A)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (DaggerSSet.forget.mapIso (e.app A))
    · simp
    · simp
    · simpa only [Category.id_comp] using hu
    · change FreeDaggerPushout.inr A ≫ (e.hom.app A).hom =
        𝟙 _ ≫ (FreeDaggerPushout.inr A ≫ (e.hom.app A).hom)
      simp
  · change adj.unit.app A ≫ (F.obj A).dagger =
      SSet.opFunctorCompOpFunctorIso.inv.app A ≫
        SSet.opFunctor.map (FreeDaggerPushout.inr A ≫ (e.hom.app A).hom)
    rw [← hu, Category.assoc, he, ← Category.assoc,
      FreeDaggerPushout.inl_daggerMap A, Category.assoc, ← SSet.opFunctor.map_comp]
  · change (FreeDaggerPushout.inr A ≫ (e.hom.app A).hom) ≫ (F.obj A).dagger =
      SSet.opFunctor.map (adj.unit.app A)
    rw [Category.assoc, he, ← Category.assoc, FreeDaggerPushout.inr_daggerMap,
      ← SSet.opFunctor.map_comp, hu]

end DaggerModels
