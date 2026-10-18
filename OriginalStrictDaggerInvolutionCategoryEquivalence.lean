import OriginalStrictGroupoidDaggerInvolutionEquivalence
import OriginalSimplicialDaggerGroupoidCompletionAdjunction

/-!
# Equivalence of the original strict dagger groupoids and object-fixing involutions

Objects and morphisms retain the original enriched categories and enriched functors.
The proved inverse-dagger equivalence supplies both functors and their full natural
isomorphisms. This equivalence does not yet transport or construct a model structure.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction
open DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
universe u

namespace DaggerOriginalStrictDaggerInvolutionCategoryEquivalence

noncomputable section

/-- The original strict groupoid equipped with an object-fixing covariant involution. -/
structure StrictInvolutiveGroupoid where
  underlying : SimplicialCat.{u, u}
  strict : IsStrictGroupoid underlying
  involution : ObjectFixedInvolution underlying

/-- Morphisms are exactly the original enriched functors intertwining the involutions. -/
structure InvolutiveHom (C D : StrictInvolutiveGroupoid.{u}) where
  underlying : C.underlying ⟶ D.underlying
  equivariant : PreservesInvolution C.involution D.involution underlying

/-- The underlying original enriched functor determines the full equivariant morphism. -/
theorem involutiveHom_ext {C D : StrictInvolutiveGroupoid.{u}} {F G : InvolutiveHom C D}
    (h : F.underlying = G.underlying) : F = G := by
  cases F
  cases G
  dsimp only at h
  cases h
  rfl

/-- The identity is the same original enriched identity. -/
def involutiveId (C : StrictInvolutiveGroupoid.{u}) : InvolutiveHom C C where
  underlying := 𝟙 C.underlying
  equivariant x y := by simp

/-- Composition is the same original enriched composition of functors. -/
def involutiveComp {C D E : StrictInvolutiveGroupoid.{u}}
    (F : InvolutiveHom C D) (G : InvolutiveHom D E) : InvolutiveHom C E where
  underlying := F.underlying ≫ G.underlying
  equivariant x y := by
    change C.involution.map x y ≫ (F.underlying.map x y ≫
        G.underlying.map (F.underlying.obj x) (F.underlying.obj y)) =
      (F.underlying.map x y ≫ G.underlying.map (F.underlying.obj x) (F.underlying.obj y)) ≫ _
    rw [← Category.assoc, F.equivariant, Category.assoc, G.equivariant, Category.assoc]
    rfl

/-- Category laws are the laws of the unchanged original enriched functors. -/
instance strictInvolutiveCategory : Category StrictInvolutiveGroupoid.{u} where
  Hom := InvolutiveHom
  id := involutiveId
  comp := involutiveComp
  id_comp F := involutiveHom_ext (Category.id_comp F.underlying)
  comp_id F := involutiveHom_ext (Category.comp_id F.underlying)
  assoc F G H := involutiveHom_ext (Category.assoc F.underlying G.underlying H.underlying)

/-- Forget only the covariant involution, retaining each exact original enriched functor. -/
def involutionForget : StrictInvolutiveGroupoid.{u} ⥤ SimplicialCat.{u, u} where
  obj C := C.underlying
  map F := F.underlying

instance involutionForget_faithful : involutionForget.{u}.Faithful where
  map_injective := involutiveHom_ext

/-- Forget only the original strict dagger, retaining each exact original enriched functor. -/
def strictDaggerForget : StrictDaggerSimplicialGroupoids.{u} ⥤ SimplicialCat.{u, u} where
  obj C := C.obj.toSimplicialCat
  map F := F.hom.toEnrichedFunctor

instance strictDaggerForget_faithful : strictDaggerForget.{u}.Faithful where
  map_injective h := (strictDaggerHomEquiv _ _).injective (DaggerSimplicialCat.Hom.ext h)

/-- Convert the original strict dagger by inverse dagger, on the same objects and Homs. -/
def daggerToInvolution : StrictDaggerSimplicialGroupoids.{u} ⥤ StrictInvolutiveGroupoid.{u} where
  obj C := ⟨C.obj.toSimplicialCat, C.property,
    involutionOfDagger C.obj.toSimplicialCat C.property C.obj.daggerStructure⟩
  map {C D} F :=
    { underlying := F.hom.toEnrichedFunctor
      equivariant := (preservesDagger_iff_preservesInvolution C.property D.property
        C.obj.daggerStructure D.obj.daggerStructure F.hom.toEnrichedFunctor).mp F.hom.map_dagger }

/-- Recover the original dagger by native inversion of the object-fixing involution. -/
def involutionToDagger : StrictInvolutiveGroupoid.{u} ⥤ StrictDaggerSimplicialGroupoids.{u} where
  obj C := ⟨⟨C.underlying, daggerOfInvolution C.underlying C.strict C.involution⟩, C.strict⟩
  map {C D} F := ObjectProperty.homMk
    { toEnrichedFunctor := F.underlying
      map_dagger := by
        apply (preservesDagger_iff_preservesInvolution C.strict D.strict _ _ F.underlying).mpr
        change PreservesInvolution
          (involutionOfDagger C.underlying C.strict
            (daggerOfInvolution C.underlying C.strict C.involution))
          (involutionOfDagger D.underlying D.strict
            (daggerOfInvolution D.underlying D.strict D.involution)) F.underlying
        rw [involutionOfDagger_ofInvolution, involutionOfDagger_ofInvolution]
        exact F.equivariant }

/-- Recovering dagger returns the full original strict dagger object, including its structure. -/
theorem daggerToInvolutionToDagger_obj (C : StrictDaggerSimplicialGroupoids.{u}) :
    (daggerToInvolution ⋙ involutionToDagger).obj C = C := by
  apply ObjectProperty.FullSubcategory.ext
  change (⟨C.obj.toSimplicialCat,
    daggerOfInvolution C.obj.toSimplicialCat C.property
      (involutionOfDagger C.obj.toSimplicialCat C.property C.obj.daggerStructure)⟩ :
        DaggerSimplicialCat.{u, u}) = C.obj
  rw [daggerOfInvolution_ofDagger]

/-- Recovering the involution returns the full original strict involutive object. -/
theorem involutionToDaggerToInvolution_obj (C : StrictInvolutiveGroupoid.{u}) :
    (involutionToDagger ⋙ daggerToInvolution).obj C = C := by
  change StrictInvolutiveGroupoid.mk C.underlying C.strict
    (involutionOfDagger C.underlying C.strict
      (daggerOfInvolution C.underlying C.strict C.involution)) = C
  rw [involutionOfDagger_ofInvolution]

/-- Both functors retain precisely the original strict dagger forgetful functor. -/
theorem daggerToInvolution_forget : daggerToInvolution.{u} ⋙ involutionForget =
    strictDaggerForget := rfl

/-- Both functors retain precisely the original involutive forgetful functor. -/
theorem involutionToDagger_forget : involutionToDagger.{u} ⋙ strictDaggerForget =
    involutionForget := rfl

/-- The reconstruction equality is natural on the full original strict dagger category. -/
def daggerReconstructionIso : 𝟭 StrictDaggerSimplicialGroupoids.{u} ≅
    daggerToInvolution ⋙ involutionToDagger :=
  NatIso.ofComponents (fun C ↦ eqToIso (daggerToInvolutionToDagger_obj C).symm) (by
    intro C D F
    apply strictDaggerForget.map_injective
    simp only [Functor.map_comp, eqToIso.hom, eqToHom_map, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    rfl)

/-- The converse reconstruction equality is natural on every original equivariant functor. -/
def involutionReconstructionIso : involutionToDagger.{u} ⋙ daggerToInvolution ≅
    𝟭 StrictInvolutiveGroupoid.{u} :=
  NatIso.ofComponents (fun C ↦ eqToIso (involutionToDaggerToInvolution_obj C)) (by
    intro C D F
    apply involutionForget.map_injective
    simp only [Functor.map_comp, eqToIso.hom, eqToHom_map, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    rfl)

/-- The full original strict dagger category is equivalent to object-fixing involutions. -/
def strictDaggerInvolutionEquivalence :
    StrictDaggerSimplicialGroupoids.{u} ≌ StrictInvolutiveGroupoid.{u} :=
  CategoryTheory.Equivalence.mk daggerToInvolution involutionToDagger
    daggerReconstructionIso involutionReconstructionIso

end

end DaggerOriginalStrictDaggerInvolutionCategoryEquivalence
