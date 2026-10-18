import OriginalStrictDaggerNativeActionMappingCompatibility

/-!
# Original simplicial categories on a fixed object type

Objects carry the original enrichment on precisely O. Morphisms have the identity
object function and the original enriched Hom maps. The faithful comparison retains
these exact original categories and functors. Strict groupoids use the already proved
invertibility condition in the same original degree categories, with no model premise.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory DaggerModels
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
universe u

namespace DaggerOriginalFixedObjectSimplicialCategories

noncomputable section

/-- The original simplicial enrichment on exactly the fixed object type O. -/
structure FixedSimplicialCategory (O : Type u) where
  enriched : EnrichedCategory SSet.{u} O

/-- Retain the same fixed objects, original Hom, identity and composition. -/
def original (O : Type u) (C : FixedSimplicialCategory O) : SimplicialCat.{u, u} :=
  ⟨O, C.enriched⟩

/-- Original enriched Hom maps with the identity function on the fixed object type. -/
structure FixedHom {O : Type u} (C D : FixedSimplicialCategory O) where
  map : ∀ x y, C.enriched.Hom x y ⟶ D.enriched.Hom x y
  map_id : ∀ x, C.enriched.id x ≫ map x x = D.enriched.id x
  map_comp : ∀ x y z, C.enriched.comp x y z ≫ map x z =
    (map x y ⊗ₘ map y z) ≫ D.enriched.comp x y z

/-- Fixed-object arrows are actual original enriched functors with identity object function. -/
def originalHom {O : Type u} {C D : FixedSimplicialCategory O} (F : FixedHom C D) :
    original O C ⟶ original O D where
  obj x := x
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

/-- Equality of all original Hom maps determines a fixed-object functor. -/
theorem fixedHom_ext {O : Type u} {C D : FixedSimplicialCategory O} {F G : FixedHom C D}
    (h : ∀ x y, F.map x y = G.map x y) : F = G := by
  have he : F.map = G.map := funext fun x ↦ funext fun y ↦ h x y
  cases F
  cases G
  dsimp only at he
  cases he
  rfl

/-- Equality of whole original functors retains equality of all fixed-object Hom maps. -/
theorem originalHom_injective {O : Type u} {C D : FixedSimplicialCategory O} :
    Function.Injective (originalHom (C := C) (D := D)) := by
  intro F G h
  apply fixedHom_ext
  intro x y
  exact eq_of_heq
    (DaggerOriginalStrictGroupoidObjectFixedC2Actions.enrichedFunctor_map_heq h x y)

/-- The same original identity functor, on the fixed objects. -/
def fixedId {O : Type u} (C : FixedSimplicialCategory O) : FixedHom C C where
  map := (𝟙 (original O C) : original O C ⟶ original O C).map
  map_id := (𝟙 (original O C) : original O C ⟶ original O C).map_id
  map_comp := (𝟙 (original O C) : original O C ⟶ original O C).map_comp

/-- Compose the same original functors; their object functions remain identity. -/
def fixedComp {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : FixedHom C D) (G : FixedHom D E) : FixedHom C E where
  map := (originalHom F ≫ originalHom G).map
  map_id := (originalHom F ≫ originalHom G).map_id
  map_comp := (originalHom F ≫ originalHom G).map_comp

/-- Native category laws follow from the unchanged original enriched functors. -/
instance fixedCategory (O : Type u) : Category (FixedSimplicialCategory O) where
  Hom := FixedHom
  id := fixedId
  comp := fixedComp
  id_comp F := originalHom_injective (Category.id_comp (originalHom F))
  comp_id F := originalHom_injective (Category.comp_id (originalHom F))
  assoc F G H := originalHom_injective
    (Category.assoc (originalHom F) (originalHom G) (originalHom H))

/-- The original fixed-object category maps faithfully into the unchanged original category. -/
def fixedToOriginal (O : Type u) : FixedSimplicialCategory O ⥤ SimplicialCat.{u, u} where
  obj := original O
  map := originalHom

instance fixedToOriginal_faithful (O : Type u) : (fixedToOriginal O).Faithful where
  map_injective h := originalHom_injective h

/-- Strictness is invertibility in the exact original degree categories on O. -/
def IsStrictFixed {O : Type u} (C : FixedSimplicialCategory O) : Prop :=
  IsStrictGroupoid (original O C)

/-- The original simplicial groupoids on exactly O and identity-object-function arrows. -/
abbrev FixedStrictGroupoids (O : Type u) := ObjectProperty.FullSubcategory (IsStrictFixed (O := O))

/-- The faithful comparison keeps the original groupoids and identity-object-function arrows. -/
def fixedStrictToOriginal (O : Type u) : FixedStrictGroupoids O ⥤ StrictSimplicialGroupoids.{u}
    where
  obj C := ⟨original O C.obj, C.property⟩
  map F := ObjectProperty.homMk (originalHom F.hom)

instance fixedStrictToOriginal_faithful (O : Type u) : (fixedStrictToOriginal O).Faithful where
  map_injective h := ObjectProperty.hom_ext _
    (originalHom_injective (congrArg (fun F ↦ F.hom) h))

/-- Every fixed strict groupoid has native Kan original mapping objects, without extra premises. -/
theorem fixedStrictHom_kan {O : Type u} (C : FixedStrictGroupoids O) (x y : O) :
    (C.obj.enriched.Hom x y).KanComplex :=
  DaggerOriginalStrictSimplicialGroupoidMappingKan.strictHom_kan (original O C.obj) C.property x y

end

end DaggerOriginalFixedObjectSimplicialCategories
