import OriginalFixedObjectAmbientDaggerModel

/-!
# Restriction of the existing full cofree dagger adjunction to the actual fixed object set

Reuse DaggerSimplicialCat.Cofree without reconstructing opposites, composition or
dagger. Its original Hom is C(x,y) times C(y,x), and its maps keep the given
identity object function. The full restricted adjunction retains every Hom map.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
universe u
namespace DaggerOriginalFixedObjectAmbientDaggerCofreeAdjunction
noncomputable section

/-- Forget just the dagger on the original full fixed-object category. -/
def ambientForget (O : Type u) : FixedDaggerCategory O ⥤ FixedSimplicialCategory O where
  obj C := C.underlying
  map F := F.underlying

/-- The existing full native cofree category has precisely the original fixed object type. -/
def ambientCofreeObject {O : Type u} (C : FixedSimplicialCategory O) : FixedDaggerCategory O :=
  ⟨⟨(DaggerSimplicialCat.Cofree.category (original O C)).enriched⟩,
    (DaggerSimplicialCat.Cofree.category (original O C)).daggerStructure⟩

/-- Restrict the full existing cofree functor on the actual original identity-object map. -/
def ambientCofreeMap {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    ambientCofreeObject C ⟶ ambientCofreeObject D where
  underlying :=
    { map := (DaggerSimplicialCat.Cofree.functor.map (originalHom F)).map
      map_id := (DaggerSimplicialCat.Cofree.functor.map (originalHom F)).map_id
      map_comp := (DaggerSimplicialCat.Cofree.functor.map (originalHom F)).map_comp }
  map_dagger := (DaggerSimplicialCat.Cofree.functor.map (originalHom F)).map_dagger

/-- The whole existing cofree functor restricted to the exact original fixed objects. -/
def ambientCofree (O : Type u) : FixedSimplicialCategory O ⥤ FixedDaggerCategory O where
  obj := ambientCofreeObject
  map := ambientCofreeMap
  map_id C := by
    apply originalDaggerHom_injective
    change DaggerSimplicialCat.Cofree.functor.map (𝟙 (original O C)) = 𝟙 _
    exact DaggerSimplicialCat.Cofree.functor.map_id (original O C)
  map_comp F G := originalDaggerHom_injective
    (DaggerSimplicialCat.Cofree.functor.map_comp (originalHom F) (originalHom G))

/-- The original native projection forgets the second cofree Hom coordinate. -/
def project {O : Type u} {C : FixedDaggerCategory O} {D : FixedSimplicialCategory O}
    (F : C ⟶ ambientCofreeObject D) : C.underlying ⟶ D where
  map := (DaggerSimplicialCat.Cofree.project (D := originalDagger C)
        (C := original O D) (originalDaggerHom F)).map
  map_id := (DaggerSimplicialCat.Cofree.project (D := originalDagger C)
        (C := original O D) (originalDaggerHom F)).map_id
  map_comp := (DaggerSimplicialCat.Cofree.project (D := originalDagger C)
        (C := original O D) (originalDaggerHom F)).map_comp

/-- The original native cofree lift keeps the entire original fixed-object functor. -/
def lift {O : Type u} {C : FixedDaggerCategory O} {D : FixedSimplicialCategory O}
    (F : C.underlying ⟶ D) : C ⟶ ambientCofreeObject D where
  underlying :=
    { map := (DaggerSimplicialCat.Cofree.lift 
        (D := originalDagger C) (original O D) (originalHom F)).map
      map_id := (DaggerSimplicialCat.Cofree.lift 
        (D := originalDagger C) (original O D) (originalHom F)).map_id
      map_comp := (DaggerSimplicialCat.Cofree.lift 
        (D := originalDagger C) (original O D) (originalHom F)).map_comp }
  map_dagger := (DaggerSimplicialCat.Cofree.lift 
        (D := originalDagger C) (original O D) (originalHom F)).map_dagger

/-- Restrict the proved native inverse identities, preserving all original Hom maps. -/
def homEquiv {O : Type u} (C : FixedDaggerCategory O) (D : FixedSimplicialCategory O) :
    (C.underlying ⟶ D) ≃ (C ⟶ ambientCofreeObject D) where
  toFun := lift
  invFun := project
  left_inv F := by
    apply originalHom_injective
    change DaggerSimplicialCat.Cofree.project
      (DaggerSimplicialCat.Cofree.lift (D := originalDagger C) (original O D) (originalHom F)) = _
    exact DaggerSimplicialCat.Cofree.project_lift
      (D := originalDagger C) (original O D) (originalHom F)
  right_inv F := by
    apply originalDaggerHom_injective
    change DaggerSimplicialCat.Cofree.lift (D := originalDagger C) (original O D)
      (DaggerSimplicialCat.Cofree.project (C := original O D) (originalDaggerHom F)) = _
    exact DaggerSimplicialCat.Cofree.lift_project (D := originalDagger C)
      (C := original O D) (originalDaggerHom F)

/-- Forgetting the actual ambient dagger is left adjoint to the unchanged native cofree functor. -/
def ambientForgetCofreeAdjunction (O : Type u) : ambientForget O ⊣ ambientCofree O :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro C C' D F G
        apply fixedHom_ext
        intro x y
        apply NatTrans.ext
        funext n a
        rfl
      homEquiv_naturality_right := by
        intro C D D' F G
        apply originalDaggerHom_injective
        exact DaggerSimplicialCat.Cofree.homEquiv_naturality_right
          (D := originalDagger C) (originalHom F) (originalHom G) }

end
end DaggerOriginalFixedObjectAmbientDaggerCofreeAdjunction
