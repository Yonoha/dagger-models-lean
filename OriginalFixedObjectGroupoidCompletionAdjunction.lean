import OriginalFixedObjectDaggerActionEquivalence
import OriginalSimplicialDaggerGroupoidCompletionAdjunction

/-!
# The original completion-inclusion adjunctions on the fixed object type

Restrict the already verified full completion, localization and unique lifts to O.
The fixed-object arrows keep the identity object function. Both ordinary and dagger
adjunctions use the same original universal properties, without an enriched or model
category premise. This is not yet a simplicial Quillen adjunction.
-/

set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalSimplicialGroupoidCompletion
open DaggerOriginalSimplicialGroupoidCompletionFunctor
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalSimplicialGroupoidCompletionAdjunction
open DaggerOriginalSimplicialGroupoidCompletionDagger
open DaggerOriginalSimplicialGroupoidCompletionDaggerFunctor
open DaggerOriginalSimplicialDaggerGroupoidCompletionUniversal
open DaggerOriginalSimplicialDaggerGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
universe u

namespace DaggerOriginalFixedObjectGroupoidCompletionAdjunction

noncomputable section

/-- The original completion enrichment, with exactly the same fixed object type O. -/
def fixedCompleted {O : Type u} (C : FixedSimplicialCategory O) : FixedSimplicialCategory O :=
  ⟨(completion (original O C)).enriched⟩

/-- The full original completion map restricts to the identity object function on O. -/
def fixedCompletionMap {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    fixedCompleted C ⟶ fixedCompleted D where
  map := (completionMap (originalHom F)).map
  map_id := (completionMap (originalHom F)).map_id
  map_comp := (completionMap (originalHom F)).map_comp

/-- The actual original completion functor into fixed-object strict simplicial groupoids. -/
def fixedCompletion (O : Type u) : FixedSimplicialCategory O ⥤ FixedStrictGroupoids O where
  obj C := ⟨fixedCompleted C, completion_isStrictGroupoid (original O C)⟩
  map F := ObjectProperty.homMk (fixedCompletionMap F)
  map_id C := ObjectProperty.hom_ext _ (originalHom_injective (completionMap_id (original O C)))
  map_comp F G := ObjectProperty.hom_ext _
    (originalHom_injective (completionMap_comp (originalHom F) (originalHom G)))

/-- Include the same original strict fixed-object groupoids, without changing their arrows. -/
def fixedInclusion (O : Type u) : FixedStrictGroupoids O ⥤ FixedSimplicialCategory O :=
  ObjectProperty.ι IsStrictFixed

/-- The same original localization is a fixed-object functor. -/
def fixedLocalization {O : Type u} (C : FixedSimplicialCategory O) : C ⟶ fixedCompleted C where
  map := (localization (original O C)).map
  map_id := (localization (original O C)).map_id
  map_comp := (localization (original O C)).map_comp

/-- The full original unique lift preserves the identity object function of its input. -/
def fixedLift {O : Type u} {C : FixedSimplicialCategory O} (D : FixedStrictGroupoids O)
    (F : C ⟶ D.obj) : fixedCompleted C ⟶ D.obj where
  map := (lift D.property (originalHom F)).map
  map_id := (lift D.property (originalHom F)).map_id
  map_comp := (lift D.property (originalHom F)).map_comp

/-- The exact fixed-object universal property of the same original completion. -/
def fixedCompletionHomEquiv {O : Type u} (C : FixedSimplicialCategory O)
    (D : FixedStrictGroupoids O) : ((fixedCompletion O).obj C ⟶ D) ≃ (C ⟶ D.obj) where
  toFun F := fixedLocalization C ≫ F.hom
  invFun F := ObjectProperty.homMk (fixedLift D F)
  left_inv F := ObjectProperty.hom_ext _ (originalHom_injective
    (lift_unique D.property (localization (original O C) ≫ originalHom F.hom)
      (originalHom F.hom) rfl).symm)
  right_inv F := originalHom_injective (lift_spec D.property (originalHom F))

/-- Actual completion and inclusion on O are adjoint by the full original universal property. -/
def fixedCompletionInclusionAdjunction (O : Type u) : fixedCompletion O ⊣ fixedInclusion O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fixedCompletionHomEquiv
      homEquiv_naturality_left_symm := by
        intro C C' D F G
        apply ObjectProperty.hom_ext _
        apply originalHom_injective
        change lift D.property (originalHom F ≫ originalHom G) =
          completionMap (originalHom F) ≫ lift D.property (originalHom G)
        symm
        apply lift_unique D.property
        rw [← Category.assoc, localization_naturality, Category.assoc, lift_spec]
      homEquiv_naturality_right := by
        intro C D D' F G
        exact Category.assoc (fixedLocalization C) F.hom G.hom }

/-- The original dagger completion on the same fixed object type and original completed Hom. -/
def fixedDaggerCompleted {O : Type u} (C : FixedDaggerCategory O) : FixedDaggerCategory O :=
  ⟨⟨(daggerCompletion (originalDagger C)).enriched⟩,
    (daggerCompletion (originalDagger C)).daggerStructure⟩

/-- The same original completion map of a fixed dagger functor, with identity object function. -/
def fixedDaggerCompletionMap {O : Type u} {C D : FixedDaggerCategory O} (F : C ⟶ D) :
    fixedDaggerCompleted C ⟶ fixedDaggerCompleted D where
  underlying :=
    { map := (daggerCompletionMap (originalDaggerHom F)).map
      map_id := (daggerCompletionMap (originalDaggerHom F)).map_id
      map_comp := (daggerCompletionMap (originalDaggerHom F)).map_comp }
  map_dagger := (daggerCompletionMap (originalDaggerHom F)).map_dagger

/-- The full original dagger completion functor lands in fixed-object strict dagger groupoids. -/
def fixedDaggerCompletion (O : Type u) :
    FixedDaggerCategory O ⥤ FixedStrictDaggerGroupoids O where
  obj C := ⟨fixedDaggerCompleted C, completion_isStrictGroupoid (original O C.underlying)⟩
  map F := ObjectProperty.homMk (fixedDaggerCompletionMap F)
  map_id C := ObjectProperty.hom_ext _
    (originalDaggerHom_injective (daggerCompletionMap_id (originalDagger C)))
  map_comp F G := ObjectProperty.hom_ext _
    (originalDaggerHom_injective
      (daggerCompletionMap_comp (originalDaggerHom F) (originalDaggerHom G)))

/-- Include exactly the same fixed-object strict dagger groupoids and original dagger functors. -/
def fixedDaggerInclusion (O : Type u) : FixedStrictDaggerGroupoids O ⥤ FixedDaggerCategory O :=
  ObjectProperty.ι IsStrictFixedDagger

/-- The actual original dagger localization preserves the fixed objects O. -/
def fixedDaggerLocalization {O : Type u} (C : FixedDaggerCategory O) : C ⟶ fixedDaggerCompleted C
    where
  underlying :=
    { map := (daggerLocalization (originalDagger C)).map
      map_id := (daggerLocalization (originalDagger C)).map_id
      map_comp := (daggerLocalization (originalDagger C)).map_comp }
  map_dagger := (daggerLocalization (originalDagger C)).map_dagger

/-- The same full original dagger lift, preserving the input's identity object function. -/
def fixedDaggerLift {O : Type u} {C : FixedDaggerCategory O} (D : FixedStrictDaggerGroupoids O)
    (F : C ⟶ D.obj) : fixedDaggerCompleted C ⟶ D.obj where
  underlying :=
    { map := (daggerLift (D := originalDagger D.obj) D.property (originalDaggerHom F)).map
      map_id := (daggerLift (D := originalDagger D.obj) D.property (originalDaggerHom F)).map_id
      map_comp :=
        (daggerLift (D := originalDagger D.obj) D.property (originalDaggerHom F)).map_comp }
  map_dagger := (daggerLift (D := originalDagger D.obj) D.property (originalDaggerHom F)).map_dagger

/-- The exact full original dagger extension equivalence restricted to the fixed object type. -/
def fixedDaggerCompletionHomEquiv {O : Type u} (C : FixedDaggerCategory O)
    (D : FixedStrictDaggerGroupoids O) :
    ((fixedDaggerCompletion O).obj C ⟶ D) ≃ (C ⟶ D.obj) where
  toFun F := fixedDaggerLocalization C ≫ F.hom
  invFun F := ObjectProperty.homMk (fixedDaggerLift D F)
  left_inv F := ObjectProperty.hom_ext _ (originalDaggerHom_injective
    (daggerLift_unique (D := originalDagger D.obj) D.property
      (daggerLocalization (originalDagger C) ≫ originalDaggerHom F.hom)
      (originalDaggerHom F.hom) rfl).symm)
  right_inv F := originalDaggerHom_injective
    (daggerLift_spec (D := originalDagger D.obj) D.property (originalDaggerHom F))

/-- Actual dagger completion and inclusion on O are adjoint, without model assumptions. -/
def fixedDaggerCompletionInclusionAdjunction (O : Type u) :
    fixedDaggerCompletion O ⊣ fixedDaggerInclusion O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fixedDaggerCompletionHomEquiv
      homEquiv_naturality_left_symm := by
        intro C C' D F G
        apply ObjectProperty.hom_ext _
        apply originalDaggerHom_injective
        change daggerLift (D := originalDagger D.obj) D.property
          (originalDaggerHom F ≫ originalDaggerHom G) =
          daggerCompletionMap (originalDaggerHom F) ≫
            daggerLift (D := originalDagger D.obj) D.property (originalDaggerHom G)
        symm
        apply daggerLift_unique (D := originalDagger D.obj) D.property
        rw [← Category.assoc, daggerLocalization_naturality, Category.assoc, daggerLift_spec]
      homEquiv_naturality_right := by
        intro C D D' F G
        exact Category.assoc (fixedDaggerLocalization C) F.hom G.hom }

end

end DaggerOriginalFixedObjectGroupoidCompletionAdjunction
