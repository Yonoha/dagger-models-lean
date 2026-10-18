import ChosenEnrichedFunctorMapEquality

open CategoryTheory EnrichedCategory MonoidalCategory

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

/-- Thin inverse constructor for specified object and full Hom isos; no new choices or model data. -/
structure SpecifiedEnrichedIsoData (A D : DaggerModels.SimplicialCat.{u,u}) where
  objects : A.Obj ≃ D.Obj
  homs : ∀ x y : A.Obj, (x ⟶[SSet.{u}] y) ≅ (objects x ⟶[SSet.{u}] objects y)
  hom_id : ∀ x : A.Obj, eId SSet x ≫ (homs x x).hom = eId SSet (objects x)
  hom_comp : ∀ x y z : A.Obj, eComp SSet x y z ≫ (homs x z).hom =
    ((homs x y).hom ⊗ₘ (homs y z).hom) ≫ eComp SSet (objects x) (objects y) (objects z)

private theorem eId_transport {D : DaggerModels.SimplicialCat.{u,u}}
    (a b : D.Obj) (h : a = b) : eId SSet a ≫ targetHomTransport h h = eId SSet b := by
  cases h
  simp only [targetHomTransport, eqToHom_refl, Category.comp_id]

private theorem eComp_transport {D : DaggerModels.SimplicialCat.{u,u}}
    (a b c a' b' c' : D.Obj) (ha : a = a') (hb : b = b') (hc : c = c') :
    eComp SSet a b c ≫ targetHomTransport ha hc =
      (targetHomTransport ha hb ⊗ₘ targetHomTransport hb hc) ≫ eComp SSet a' b' c' := by
  cases ha
  cases hb
  cases hc
  simp only [targetHomTransport, eqToHom_refl, id_tensorHom_id, Category.comp_id,
    Category.id_comp]

private theorem sourceMap_transport {A D : DaggerModels.SimplicialCat.{u,u}}
    (F : A ⟶ D) {x y x' y' : A.Obj} (hx : x = x') (hy : y = y') :
    targetHomTransport hx hy ≫ F.map x' y' =
      F.map x y ≫ targetHomTransport (congrArg F.obj hx) (congrArg F.obj hy) := by
  cases hx
  cases hy
  rfl

namespace SpecifiedEnrichedIsoData

variable {A D : DaggerModels.SimplicialCat.{u,u}} (S : SpecifiedEnrichedIsoData A D)

def forward : A ⟶ D where
  obj := S.objects
  map x y := (S.homs x y).hom
  map_id := S.hom_id
  map_comp := S.hom_comp

/-- Source inverse labels and both target endpoint casts are specified by the same equivalence. -/
def inverseForwardHom (a b : D.Obj) :
    (S.objects.symm a ⟶[SSet.{u}] S.objects.symm b) ≅ (a ⟶[SSet.{u}] b) :=
  S.homs (S.objects.symm a) (S.objects.symm b) ≪≫
    eqToIso (by rw [S.objects.apply_symm_apply, S.objects.apply_symm_apply])

theorem inverseForwardHom_identity (a : D.Obj) :
    eId SSet (S.objects.symm a) ≫ (S.inverseForwardHom a a).hom = eId SSet a := by
  change eId SSet (S.objects.symm a) ≫ (S.homs _ _).hom ≫
    targetHomTransport (S.objects.apply_symm_apply a) (S.objects.apply_symm_apply a) = _
  rw [← Category.assoc, S.hom_id]
  exact eId_transport _ _ _

theorem inverseForwardHom_composition (a b c : D.Obj) :
    eComp SSet (S.objects.symm a) (S.objects.symm b) (S.objects.symm c) ≫
        (S.inverseForwardHom a c).hom =
      ((S.inverseForwardHom a b).hom ⊗ₘ (S.inverseForwardHom b c).hom) ≫ eComp SSet a b c := by
  change eComp SSet (S.objects.symm a) (S.objects.symm b) (S.objects.symm c) ≫
      (S.homs _ _).hom ≫ targetHomTransport (S.objects.apply_symm_apply a)
        (S.objects.apply_symm_apply c) = _
  rw [← Category.assoc, S.hom_comp, Category.assoc,
    eComp_transport _ _ _ a b c (S.objects.apply_symm_apply a)
      (S.objects.apply_symm_apply b) (S.objects.apply_symm_apply c),
    ← Category.assoc, tensorHom_comp_tensorHom]
  rfl

def inverse : D ⟶ A where
  obj := S.objects.symm
  map a b := (S.inverseForwardHom a b).inv
  map_id a := by
    apply (cancel_mono (S.inverseForwardHom a a).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, S.inverseForwardHom_identity]
  map_comp a b c := by
    apply (cancel_mono (S.inverseForwardHom a c).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      S.inverseForwardHom_composition, ← Category.assoc, tensorHom_comp_tensorHom,
      Iso.inv_hom_id, Iso.inv_hom_id]
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp]

theorem inverse_forward : S.inverse ≫ S.forward = 𝟙 D := by
  have ho : ∀ a : D.Obj, (S.inverse ≫ S.forward).obj a = a :=
    fun a ↦ S.objects.apply_symm_apply a
  apply EnrichedFunctor.ext SSet ho
  intro a b
  change (S.inverseForwardHom a b).inv ≫ (S.inverseForwardHom a b).hom = 𝟙 _
  exact Iso.inv_hom_id _

theorem inverseForwardHom_transport (x y : A.Obj) :
    (S.inverseForwardHom (S.objects x) (S.objects y)).hom =
      targetHomTransport (S.objects.symm_apply_apply x) (S.objects.symm_apply_apply y) ≫
        S.forward.map x y :=
  (sourceMap_transport S.forward (S.objects.symm_apply_apply x)
    (S.objects.symm_apply_apply y)).symm

theorem forward_inverse : S.forward ≫ S.inverse = 𝟙 A := by
  have ho : ∀ x : A.Obj, (S.forward ≫ S.inverse).obj x = x :=
    fun x ↦ S.objects.symm_apply_apply x
  apply EnrichedFunctor.ext SSet ho
  intro x y
  apply (cancel_mono (S.homs x y).hom).mp
  change ((S.homs x y).hom ≫ (S.inverseForwardHom (S.objects x) (S.objects y)).inv ≫
    targetHomTransport (S.objects.symm_apply_apply x) (S.objects.symm_apply_apply y)) ≫
    S.forward.map x y = 𝟙 _ ≫ S.forward.map x y
  rw [Category.assoc, Category.assoc, ← S.inverseForwardHom_transport,
    Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  rfl

def iso : A ≅ D where
  hom := S.forward
  inv := S.inverse
  hom_inv_id := S.forward_inverse
  inv_hom_id := S.inverse_forward

end SpecifiedEnrichedIsoData

end

end DaggerChosenRigidificationNecklace
