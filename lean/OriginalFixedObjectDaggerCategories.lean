import OriginalFixedObjectSimplicialCategories

/-!
# Original dagger simplicial categories on the fixed object type O

Both dagger objects and dagger functors retain the original enrichment on O.
Morphisms have the identity object function and preserve the exact original dagger.
Strict groupoids use the unchanged original degree invertibility predicate.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction
open DaggerOriginalStrictGroupoidDaggerInvolutionEquivalence
universe u

namespace DaggerOriginalFixedObjectDaggerCategories

noncomputable section

/-- Dagger on exactly the original fixed-object simplicial enrichment. -/
structure FixedDaggerCategory (O : Type u) where
  underlying : FixedSimplicialCategory O
  dagger : @DaggerSimplicialStructure O underlying.enriched

/-- The unchanged original dagger category, on exactly O. -/
def originalDagger {O : Type u} (C : FixedDaggerCategory O) : DaggerSimplicialCat.{u, u} :=
  ⟨original O C.underlying, C.dagger⟩

/-- Original dagger functors with identity object function on O. -/
structure FixedDaggerHom {O : Type u} (C D : FixedDaggerCategory O) where
  underlying : FixedHom C.underlying D.underlying
  map_dagger : PreservesDagger C.dagger D.dagger (originalHom underlying)

/-- The same full original dagger functor, retaining its fixed object function. -/
def originalDaggerHom {O : Type u} {C D : FixedDaggerCategory O} (F : FixedDaggerHom C D) :
    originalDagger C ⟶ originalDagger D := ⟨originalHom F.underlying, F.map_dagger⟩

/-- A fixed dagger functor is determined by the same original fixed Hom functor. -/
theorem fixedDaggerHom_ext {O : Type u} {C D : FixedDaggerCategory O}
    {F G : FixedDaggerHom C D} (h : F.underlying = G.underlying) : F = G := by
  cases F
  cases G
  dsimp only at h
  cases h
  rfl

/-- The full original dagger functor determines the fixed dagger functor. -/
theorem originalDaggerHom_injective {O : Type u} {C D : FixedDaggerCategory O} :
    Function.Injective (originalDaggerHom (C := C) (D := D)) := by
  intro F G h
  apply fixedDaggerHom_ext
  apply originalHom_injective
  exact congrArg DaggerSimplicialCat.Hom.toEnrichedFunctor h

/-- The fixed dagger identity is the same original dagger identity. -/
def fixedDaggerId {O : Type u} (C : FixedDaggerCategory O) : FixedDaggerHom C C where
  underlying := fixedId C.underlying
  map_dagger := (𝟙 (originalDagger C) : originalDagger C ⟶ originalDagger C).map_dagger

/-- The composition is the same original dagger composition on identity object functions. -/
def fixedDaggerComp {O : Type u} {C D E : FixedDaggerCategory O}
    (F : FixedDaggerHom C D) (G : FixedDaggerHom D E) : FixedDaggerHom C E where
  underlying := fixedComp F.underlying G.underlying
  map_dagger := (originalDaggerHom F ≫ originalDaggerHom G).map_dagger

/-- Native category laws follow from the unchanged full original dagger functors. -/
instance fixedDaggerCategory (O : Type u) : Category (FixedDaggerCategory O) where
  Hom := FixedDaggerHom
  id := fixedDaggerId
  comp := fixedDaggerComp
  id_comp F := originalDaggerHom_injective (Category.id_comp (originalDaggerHom F))
  comp_id F := originalDaggerHom_injective (Category.comp_id (originalDaggerHom F))
  assoc F G H := originalDaggerHom_injective
    (Category.assoc (originalDaggerHom F) (originalDaggerHom G) (originalDaggerHom H))

/-- The faithful comparison keeps every original fixed-object dagger functor unchanged. -/
def fixedDaggerToOriginal (O : Type u) : FixedDaggerCategory O ⥤ DaggerSimplicialCat.{u, u} where
  obj := originalDagger
  map := originalDaggerHom

instance fixedDaggerToOriginal_faithful (O : Type u) : (fixedDaggerToOriginal O).Faithful where
  map_injective h := originalDaggerHom_injective h

/-- Strictness is the same original degree invertibility condition, on exactly O. -/
def IsStrictFixedDagger {O : Type u} (C : FixedDaggerCategory O) : Prop :=
  IsStrictFixed C.underlying

/-- The original fixed-object strict dagger groupoids and identity-object-function arrows. -/
abbrev FixedStrictDaggerGroupoids (O : Type u) :=
  ObjectProperty.FullSubcategory (IsStrictFixedDagger (O := O))

/-- Compare faithfully with the original full strict dagger groupoid category. -/
def fixedStrictDaggerToOriginal (O : Type u) :
    FixedStrictDaggerGroupoids O ⥤ StrictDaggerSimplicialGroupoids.{u} where
  obj C := ⟨originalDagger C.obj, C.property⟩
  map F := ObjectProperty.homMk (originalDaggerHom F.hom)

instance fixedStrictDaggerToOriginal_faithful (O : Type u) :
    (fixedStrictDaggerToOriginal O).Faithful where
  map_injective h := ObjectProperty.hom_ext _
    (originalDaggerHom_injective (congrArg (fun F ↦ F.hom) h))

/-- Forget the original fixed dagger without changing any object or Hom map. -/
def fixedStrictDaggerForget (O : Type u) : FixedStrictDaggerGroupoids O ⥤ FixedStrictGroupoids O
    where
  obj C := ⟨C.obj.underlying, C.property⟩
  map F := ObjectProperty.homMk F.hom.underlying

end

end DaggerOriginalFixedObjectDaggerCategories
