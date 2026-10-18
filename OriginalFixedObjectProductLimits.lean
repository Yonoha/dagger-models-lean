import OriginalFixedObjectDaggerProducts

/-!
# Native product limits of the original fixed-object categories

Package the already proved complete original pairing/projection laws as
Mathlib IsLimit witnesses. The chosen binary products are the literal products
on the original Hom simplicial sets, with the object set unchanged.
-/

set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectProducts DaggerOriginalFixedObjectDaggerProducts
universe u

namespace DaggerOriginalFixedObjectProductLimits

noncomputable section

/-- The original product cone satisfies the full native limiting-cone universal property. -/
def productIsLimit {O : Type u} (C D : FixedSimplicialCategory O) :
    IsLimit (BinaryFan.mk (fst C D) (snd C D)) :=
  BinaryFan.isLimitMk (fun s ↦ lift s.fst s.snd)
    (fun s ↦ lift_fst s.fst s.snd) (fun s ↦ lift_snd s.fst s.snd) (by
      intro s m hf hg
      have h := lift_eta m
      rw [hf, hg] at h
      exact h.symm)

/-- The actual same-O ordinary product supplies Mathlib's binary-product existence. -/
instance ordinaryHasBinaryProduct {O : Type u} (C D : FixedSimplicialCategory O) :
    HasBinaryProduct C D := ⟨⟨⟨BinaryFan.mk (fst C D) (snd C D), productIsLimit C D⟩⟩⟩

/-- The complete native limiting-cone witness also retains the original dagger pairing. -/
def daggerProductIsLimit {O : Type u} (C D : FixedDaggerCategory O) :
    IsLimit (BinaryFan.mk (daggerFst C D) (daggerSnd C D)) :=
  BinaryFan.isLimitMk (fun s ↦ daggerLift s.fst s.snd)
    (fun s ↦ daggerLift_fst s.fst s.snd) (fun s ↦ daggerLift_snd s.fst s.snd) (by
      intro s m hf hg
      have h := daggerLift_eta m
      rw [hf, hg] at h
      exact h.symm)

/-- The same-O dagger product supplies the actual native binary-product existence. -/
instance daggerHasBinaryProduct {O : Type u} (C D : FixedDaggerCategory O) :
    HasBinaryProduct C D :=
  ⟨⟨⟨BinaryFan.mk (daggerFst C D) (daggerSnd C D), daggerProductIsLimit C D⟩⟩⟩

/-- The original strict product cone retains the full native universal property. -/
def strictProductIsLimit {O : Type u} (C D : FixedStrictGroupoids O) :
    IsLimit (BinaryFan.mk (strictFst C D) (strictSnd C D)) :=
  BinaryFan.isLimitMk (fun s ↦ strictLift s.fst s.snd)
    (fun s ↦ strictLift_fst s.fst s.snd) (fun s ↦ strictLift_snd s.fst s.snd) (by
      intro s m hf hg
      have h := strictLift_eta m
      rw [hf, hg] at h
      exact h.symm)

/-- The actual original strict category has these native binary products. -/
instance strictHasBinaryProduct {O : Type u} (C D : FixedStrictGroupoids O) :
    HasBinaryProduct C D :=
  ⟨⟨⟨BinaryFan.mk (strictFst C D) (strictSnd C D), strictProductIsLimit C D⟩⟩⟩

/-- The actual strict dagger cone is a limiting cone in the unchanged original category. -/
def strictDaggerProductIsLimit {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    IsLimit (BinaryFan.mk (strictDaggerFst C D) (strictDaggerSnd C D)) :=
  BinaryFan.isLimitMk (fun s ↦ strictDaggerLift s.fst s.snd)
    (fun s ↦ strictDaggerLift_fst s.fst s.snd)
    (fun s ↦ strictDaggerLift_snd s.fst s.snd) (by
      intro s m hf hg
      have h := strictDaggerLift_eta m
      rw [hf, hg] at h
      exact h.symm)

/-- Native binary-product existence retains the same strict dagger objects and arrows. -/
instance strictDaggerHasBinaryProduct {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    HasBinaryProduct C D :=
  ⟨⟨⟨BinaryFan.mk (strictDaggerFst C D) (strictDaggerSnd C D),
    strictDaggerProductIsLimit C D⟩⟩⟩

/-- Identify Mathlib's chosen product with the literal original strict product. -/
def strictProductIso {O : Type u} (C D : FixedStrictGroupoids O) :
    (C ⨯ D) ≅ strictProduct C D :=
  (limit.isLimit (pair C D)).conePointUniqueUpToIso (strictProductIsLimit C D)

/-- The product comparison retains the exact first original projection. -/
theorem strictProductIso_hom_fst {O : Type u} (C D : FixedStrictGroupoids O) :
    (strictProductIso C D).hom ≫ strictFst C D = prod.fst :=
  (limit.isLimit (pair C D)).conePointUniqueUpToIso_hom_comp
    (strictProductIsLimit C D) ⟨.left⟩

/-- The product comparison retains the exact second original projection. -/
theorem strictProductIso_hom_snd {O : Type u} (C D : FixedStrictGroupoids O) :
    (strictProductIso C D).hom ≫ strictSnd C D = prod.snd :=
  (limit.isLimit (pair C D)).conePointUniqueUpToIso_hom_comp
    (strictProductIsLimit C D) ⟨.right⟩

/-- Identify Mathlib's chosen product with the literal original strict dagger product. -/
def strictDaggerProductIso {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    (C ⨯ D) ≅ strictDaggerProduct C D :=
  (limit.isLimit (pair C D)).conePointUniqueUpToIso (strictDaggerProductIsLimit C D)

/-- The dagger product comparison retains the exact first original projection. -/
theorem strictDaggerProductIso_hom_fst {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    (strictDaggerProductIso C D).hom ≫ strictDaggerFst C D = prod.fst :=
  (limit.isLimit (pair C D)).conePointUniqueUpToIso_hom_comp
    (strictDaggerProductIsLimit C D) ⟨.left⟩

/-- The dagger product comparison retains the exact second original projection. -/
theorem strictDaggerProductIso_hom_snd {O : Type u} (C D : FixedStrictDaggerGroupoids O) :
    (strictDaggerProductIso C D).hom ≫ strictDaggerSnd C D = prod.snd :=
  (limit.isLimit (pair C D)).conePointUniqueUpToIso_hom_comp
    (strictDaggerProductIsLimit C D) ⟨.right⟩

end

end DaggerOriginalFixedObjectProductLimits
