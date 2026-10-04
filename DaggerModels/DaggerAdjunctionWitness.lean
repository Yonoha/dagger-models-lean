import DaggerModels.ActualDaggerFreeComparison

/-!
# Exact witnesses for the ordinary free dagger and lifted rigidification adjunctions

The witness definition is the complete frozen Mathlib-only Challenge definition.
Its data use the actual existing free functors and the original rigidification
adjunction; no model structure or ordinary-category pushout claim is added.
-/

open CategoryTheory
universe u
noncomputable section

namespace DaggerModels

/-- The actual ordinary free dagger adjunction retains the original objects and unit. -/
theorem exists_ordinaryFreeDaggerAdjunction :
    ∃ L : SimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u},
      ∃ A : L ⊣ DaggerSimplicialCat.forget,
        ∀ C : SimplicialCat.{u, u}, (L.obj C).Obj = C.Obj ∧
          HEq (A.unit.app C).obj (id : C.Obj → C.Obj) := by
  refine ⟨OrdinaryFreeDagger.functor, OrdinaryFreeDagger.adjunction, ?_⟩
  intro C
  refine ⟨OrdinaryFreeDagger.functor_obj_Obj C, ?_⟩
  rw [OrdinaryFreeDagger.adjunction_unit]
  rfl

namespace OrdinaryRigidification

structure DaggerLiftWitness where
  freeSSet : SSet.{u} ⥤ DaggerSSet.{u}
  freeSSetAdjunction : freeSSet ⊣ DaggerSSet.forget
  freeSCat : SimplicialCat.{u, u} ⥤ DaggerSimplicialCat.{u, u}
  freeSCatAdjunction : freeSCat ⊣ DaggerSimplicialCat.forget
  freeSCat_objects (C : SimplicialCat.{u, u}) : (freeSCat.obj C).Obj = C.Obj
  freeSCat_unit_objects (C : SimplicialCat.{u, u}) :
    HEq (freeSCatAdjunction.unit.app C).obj (id : C.Obj → C.Obj)
  left : DaggerSSet.{u} ⥤ DaggerSimplicialCat.{u, u}
  right : DaggerSimplicialCat.{u, u} ⥤ DaggerSSet.{u}
  adjunction : left ⊣ right
  left_forget : left ⋙ DaggerSimplicialCat.forget = DaggerSSet.forget ⋙ rigidification
  right_forget : right ⋙ DaggerSSet.forget = DaggerSimplicialCat.forget ⋙ coherentNerve
  homEquiv_compatibility (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u})
      (f : left.obj X ⟶ C) :
    rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat
        ((eqToIso left_forget).inv.app X ≫ DaggerSimplicialCat.forget.map f) =
      (adjunction.homEquiv X C f).hom ≫ (eqToIso right_forget).hom.app C
  homEquiv_symm_compatibility (X : DaggerSSet.{u}) (C : DaggerSimplicialCat.{u, u})
      (g : X ⟶ right.obj C) :
    (rigidificationCoherentNerveAdjunction.homEquiv X.toSSet C.toSimplicialCat).symm
        (g.hom ≫ (eqToIso right_forget).hom.app C) =
      (eqToIso left_forget).inv.app X ≫
        DaggerSimplicialCat.forget.map ((adjunction.homEquiv X C).symm g)
  unit_compatibility (X : DaggerSSet.{u}) :
    (adjunction.unit.app X).hom ≫ (eqToIso right_forget).hom.app (left.obj X) ≫
        coherentNerve.map ((eqToIso left_forget).hom.app X) =
      rigidificationCoherentNerveAdjunction.unit.app X.toSSet
  counit_compatibility (C : DaggerSimplicialCat.{u, u}) :
    rigidification.map ((eqToIso right_forget).inv.app C) ≫
        (eqToIso left_forget).inv.app (right.obj C) ≫
        DaggerSimplicialCat.forget.map (adjunction.counit.app C) =
      rigidificationCoherentNerveAdjunction.counit.app C.toSimplicialCat
  comparison : freeSSet ⋙ left ≅ rigidification ⋙ freeSCat
  comparison_canonical : comparison = Adjunction.leftAdjointUniq
    ((freeSSetAdjunction.comp adjunction).ofNatIsoRight (eqToIso right_forget))
    (rigidificationCoherentNerveAdjunction.comp freeSCatAdjunction)
  comparison_unit (X : SSet.{u}) :
    ((freeSSetAdjunction.comp adjunction).ofNatIsoRight
        (eqToIso right_forget)).unit.app X ≫
        (DaggerSimplicialCat.forget ⋙ coherentNerve).map (comparison.hom.app X) =
      (rigidificationCoherentNerveAdjunction.comp freeSCatAdjunction).unit.app X
  comparison_counit (C : DaggerSimplicialCat.{u, u}) :
    comparison.hom.app (coherentNerve.obj C.toSimplicialCat) ≫
        (rigidificationCoherentNerveAdjunction.comp freeSCatAdjunction).counit.app C =
      ((freeSSetAdjunction.comp adjunction).ofNatIsoRight
        (eqToIso right_forget)).counit.app C


open DaggerRigidification DaggerNerve DaggerAdjunction

/-- All19 fields use actual checked data and the original ordinary Hom correspondence. -/
def daggerRigidificationLiftWitness : DaggerLiftWitness.{u} where
  freeSSet := freeDagger
  freeSSetAdjunction := freeDaggerAdjunction
  freeSCat := OrdinaryFreeDagger.functor
  freeSCatAdjunction := OrdinaryFreeDagger.adjunction
  freeSCat_objects := OrdinaryFreeDagger.functor_obj_Obj
  freeSCat_unit_objects C := by
    rw [OrdinaryFreeDagger.adjunction_unit]
    rfl
  left := daggerRigidification
  right := daggerCoherentNerve
  adjunction := daggerRigidificationCoherentNerveAdjunction
  left_forget := rfl
  right_forget := rfl
  homEquiv_compatibility X C f := by
    simpa only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp, Category.comp_id, adjunction_homEquiv] using
      (homEquiv_hom X C f).symm
  homEquiv_symm_compatibility X C g := by
    simpa only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp, Category.comp_id, adjunction_homEquiv] using
      (homEquiv_symm_toEnrichedFunctor X C g).symm
  unit_compatibility X := by
    simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
      Category.comp_id] using adjunction_unit X
  counit_compatibility C := by
    change rigidification.map (𝟙 (coherentNerve.obj C.toSimplicialCat)) ≫ 𝟙 _ ≫
        (daggerRigidificationCoherentNerveAdjunction.counit.app C).toEnrichedFunctor = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    exact adjunction_counit C
  comparison := Adjunction.leftAdjointUniq
    ((freeDaggerAdjunction.comp daggerRigidificationCoherentNerveAdjunction).ofNatIsoRight
      (Iso.refl _))
    (rigidificationCoherentNerveAdjunction.comp OrdinaryFreeDagger.adjunction)
  comparison_canonical := rfl
  comparison_unit X := Adjunction.unit_leftAdjointUniq_hom_app _ _ X
  comparison_counit C := Adjunction.leftAdjointUniq_hom_app_counit _ _ C

/-- The full frozen lift specification has the actual constructed witness. -/
theorem exists_daggerRigidificationLift : Nonempty (DaggerLiftWitness.{u}) :=
  ⟨daggerRigidificationLiftWitness⟩

end OrdinaryRigidification
end DaggerModels
