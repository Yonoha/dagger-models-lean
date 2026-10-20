import OriginalStrictDaggerGroupoidMappingAction

/-!
# Dagger structures and object-fixing involutions on the original strict groupoid

Both structures use the same original objects, simplicial Hom, identities and composition.
Native inversion turns an object-fixing covariant involution into a dagger and vice versa.
The constructions are inverse on the full structures, and preservation by each original
enriched functor is equivalent to equivariance. No model structure is assumed or transferred.
-/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidSigma
universe u

namespace DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence

noncomputable section

/-- A covariant simplicial involution on the unchanged Hom, fixing every original object. -/
structure ObjectFixedInvolution (C : SimplicialCat.{u, u}) where
  map : ∀ x y, C.enriched.Hom x y ⟶ C.enriched.Hom x y
  map_id : ∀ x, C.enriched.id x ≫ map x x = C.enriched.id x
  map_comp : ∀ x y z, C.enriched.comp x y z ≫ map x z =
    (map x y ⊗ₘ map y z) ≫ C.enriched.comp x y z
  involutive : ∀ x y, map x y ≫ map x y = 𝟙 _

/-- The involution data is an actual enriched functor with the identity object function. -/
def involutionFunctor (C : SimplicialCat.{u, u}) (s : ObjectFixedInvolution C) : C ⟶ C where
  obj x := x
  map := s.map
  map_id := s.map_id
  map_comp := s.map_comp

/-- The full original enriched functor squares to identity. -/
theorem involutionFunctor_involutive (C : SimplicialCat.{u, u}) (s : ObjectFixedInvolution C) :
    involutionFunctor C s ≫ involutionFunctor C s = 𝟙 C := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := involutionFunctor C s ≫ involutionFunctor C s) (G := 𝟙 C) (fun _ ↦ rfl)
  intro x y
  simpa only [eqToHom_refl, Category.comp_id] using s.involutive x y

/-- Recover dagger on the original Hom by inverse of the covariant involution. -/
def daggerOfInvolution (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (s : ObjectFixedInvolution C) : @DaggerSimplicialStructure C.Obj C.enriched where
  dagger x y := s.map x y ≫ strictInversionHom C hC x y
  dagger_involutive x y := by
    ext n f
    letI := strictDegreeGroupoid C hC n
    change inv ((degreeFunctor (involutionFunctor C s) n).map
      (inv ((degreeFunctor (involutionFunctor C s) n).map f))) = f
    simp only [CategoryTheory.Functor.map_inv, IsIso.inv_inv]
    exact congrFun (NatTrans.congr_app (s.involutive x y) n) f
  dagger_id x := by
    ext n p
    letI := strictDegreeGroupoid C hC n
    change inv ((degreeFunctor (involutionFunctor C s) n).map
      (@CategoryStruct.id (degreeObjects C n) (degreeCategory C n).toCategoryStruct x)) =
      @CategoryStruct.id (degreeObjects C n) (degreeCategory C n).toCategoryStruct x
    simp only [CategoryTheory.Functor.map_id, IsIso.inv_id]
    rfl
  dagger_comp x y z := by
    ext n ⟨f, g⟩
    letI := strictDegreeGroupoid C hC n
    change inv ((degreeFunctor (involutionFunctor C s) n).map (f ≫ g)) =
      inv ((degreeFunctor (involutionFunctor C s) n).map g) ≫
        inv ((degreeFunctor (involutionFunctor C s) n).map f)
    simp only [CategoryTheory.Functor.map_comp, IsIso.inv_comp]

/-- Inverse of the given original dagger is covariant involution data on the same category. -/
def involutionOfDagger (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (d : @DaggerSimplicialStructure C.Obj C.enriched) : ObjectFixedInvolution C where
  map := strictSigmaHom ⟨C, d⟩ hC
  map_id := (strictSigmaFunctor ⟨C, d⟩ hC).map_id
  map_comp := (strictSigmaFunctor ⟨C, d⟩ hC).map_comp
  involutive := strictSigmaHom_involutive ⟨C, d⟩ hC

/-- Equality of all original dagger maps determines the full original dagger structure. -/
theorem daggerStructure_ext (C : SimplicialCat.{u, u})
    {d e : @DaggerSimplicialStructure C.Obj C.enriched}
    (h : ∀ x y, d.dagger x y = e.dagger x y) : d = e := by
  have he : d.dagger = e.dagger := funext fun x ↦ funext fun y ↦ h x y
  cases d
  cases e
  dsimp only at he
  cases he
  rfl

/-- Equality of all original involution maps determines the full covariant structure. -/
theorem objectFixedInvolution_ext (C : SimplicialCat.{u, u})
    {s t : ObjectFixedInvolution C} (h : ∀ x y, s.map x y = t.map x y) : s = t := by
  have he : s.map = t.map := funext fun x ↦ funext fun y ↦ h x y
  cases s
  cases t
  dsimp only at he
  cases he
  rfl

/-- The inverse-dagger reconstruction recovers precisely the given original dagger structure. -/
theorem daggerOfInvolution_ofDagger (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (d : @DaggerSimplicialStructure C.Obj C.enriched) :
    daggerOfInvolution C hC (involutionOfDagger C hC d) = d := by
  apply daggerStructure_ext C
  intro x y
  change (d.dagger x y ≫ strictInversionHom C hC y x) ≫ strictInversionHom C hC x y =
    d.dagger x y
  rw [Category.assoc, strictInversionHom_involutive, Category.comp_id]

/-- The converse reconstruction recovers the full given covariant involution. -/
theorem involutionOfDagger_ofInvolution (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C)
    (s : ObjectFixedInvolution C) :
    involutionOfDagger C hC (daggerOfInvolution C hC s) = s := by
  apply objectFixedInvolution_ext C
  intro x y
  change (s.map x y ≫ strictInversionHom C hC x y) ≫ strictInversionHom C hC y x = s.map x y
  rw [Category.assoc, strictInversionHom_involutive, Category.comp_id]

/-- A full equivalence of dagger and object-fixing involution structures on the same strict Hom.
-/
def daggerInvolutionEquiv (C : SimplicialCat.{u, u}) (hC : IsStrictGroupoid C) :
    (@DaggerSimplicialStructure C.Obj C.enriched) ≃ ObjectFixedInvolution C where
  toFun := involutionOfDagger C hC
  invFun := daggerOfInvolution C hC
  left_inv := daggerOfInvolution_ofDagger C hC
  right_inv := involutionOfDagger_ofInvolution C hC

/-- Equivariance of the same original enriched functor with the two object-fixing involutions. -/
def PreservesInvolution {C D : SimplicialCat.{u, u}} (s : ObjectFixedInvolution C)
    (t : ObjectFixedInvolution D) (F : C ⟶ D) : Prop :=
  ∀ x y, s.map x y ≫ F.map x y = F.map x y ≫ t.map (F.obj x) (F.obj y)

/-- Dagger preservation of the same original enriched functor, with its exact target objects. -/
def PreservesDagger {C D : SimplicialCat.{u, u}}
    (d : @DaggerSimplicialStructure C.Obj C.enriched)
    (e : @DaggerSimplicialStructure D.Obj D.enriched) (F : C ⟶ D) : Prop :=
  ∀ x y, F.map x y ≫ e.dagger (F.obj x) (F.obj y) = d.dagger x y ≫ F.map y x

/-- Original dagger preservation is exactly covariant equivariance, on every original Hom. -/
theorem preservesDagger_iff_preservesInvolution {C D : SimplicialCat.{u, u}}
    (hC : IsStrictGroupoid C) (hD : IsStrictGroupoid D)
    (d : @DaggerSimplicialStructure C.Obj C.enriched)
    (e : @DaggerSimplicialStructure D.Obj D.enriched) (F : C ⟶ D) :
    PreservesDagger d e F ↔
      PreservesInvolution (involutionOfDagger C hC d) (involutionOfDagger D hD e) F := by
  constructor
  · intro h
    let F' : (⟨C, d⟩ : DaggerSimplicialCat.{u, u}) ⟶ ⟨D, e⟩ := ⟨F, h⟩
    exact strictSigmaHom_functor hC hD F'
  · intro h x y
    ext n f
    letI := strictDegreeGroupoid C hC n
    letI := strictDegreeGroupoid D hD n
    have hs := congrFun (NatTrans.congr_app (h x y) n) f
    change (degreeFunctor F n).map (inv (degreeDagger ⟨C, d⟩ n f)) =
      inv (degreeDagger ⟨D, e⟩ n ((degreeFunctor F n).map f)) at hs
    rw [CategoryTheory.Functor.map_inv] at hs
    have hi := congrArg (fun g ↦ @inv (degreeObjects D n) (degreeCategory D n)
      (F.obj x) (F.obj y) g (hD n _ _ g)) hs
    simpa only [IsIso.inv_inv] using hi.symm

end

end DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
