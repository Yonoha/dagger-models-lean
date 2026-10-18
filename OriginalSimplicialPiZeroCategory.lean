import OriginalSimplicialPiZeroLaxMonoidal
import OriginalSimplicialDegreeCategory

/-!
# The actual component category of every original simplicial category

Transport the entire original enrichment through the native component functor.
The native Type-enriched category construction gives its category laws. Hom
sets are literally the original Hom components; the identity and composition
retain their original values on every vertex. Original enriched functors and
the actual degree-zero vertex functor retain every object and Hom map.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialPiZeroLaxMonoidal DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerOriginalSimplicialPiZeroCategory
noncomputable section

/-- The same original objects, carrying their transported component enrichment. -/
def componentObjects (C : SimplicialCat.{u, u}) : Type u :=
  TransportEnrichment SSet.π₀Functor.{u} C.Obj

/-- Native transport gives the entire original component enrichment. -/
instance componentEnrichment (C : SimplicialCat.{u, u}) :
    EnrichedCategory (Type u) (componentObjects C) :=
  inferInstanceAs (EnrichedCategory (Type u) (TransportEnrichment SSet.π₀Functor.{u} C.Obj))

/-- The native ordinary category has exactly the original component Hom sets. -/
instance componentCategory (C : SimplicialCat.{u, u}) : Category.{u} (componentObjects C) :=
  categoryOfEnrichedCategoryType (componentObjects C)

/-- Retain the actual original component Hom set without replacing it by a singleton. -/
theorem componentHom_eq (C : SimplicialCat.{u, u}) (x y : componentObjects C) :
    (x ⟶ y) = (C.enriched.Hom x y).π₀ := rfl

/-- The component identity is the class of the exact original enriched identity. -/
theorem componentId_eq (C : SimplicialCat.{u, u}) (x : componentObjects C) :
    (𝟙 x) = SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) := rfl

/-- Composition descends the entire original composition, using the proved quotient pairing. -/
theorem componentComp_eq (C : SimplicialCat.{u, u}) {x y z : componentObjects C}
    (a : x ⟶ y) (b : y ⟶ z) :
    a ≫ b = SSet.mapπ₀ (C.enriched.comp x y z)
      (pairComponents (C.enriched.Hom x y) (C.enriched.Hom y z) a b) := rfl

/-- Every pair of original vertices has precisely its original composition class. -/
theorem componentComp_mk (C : SimplicialCat.{u, u}) {x y z : componentObjects C}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y z).obj (op ⦋0⦌)) :
    @CategoryStruct.comp (componentObjects C) (componentCategory C).toCategoryStruct x y z
      (SSet.π₀.mk (X := C.enriched.Hom x y) a)
      (SSet.π₀.mk (X := C.enriched.Hom y z) b) =
      SSet.π₀.mk (X := C.enriched.Hom x z)
        ((C.enriched.comp x y z).app (op ⦋0⦌) (a, b)) := rfl

/-- The actual vertex-to-component functor keeps the original objects and composition. -/
def vertexFunctor (C : SimplicialCat.{u, u}) :
    degreeObjects C (op ⦋0⦌) ⥤ componentObjects C where
  obj x := x
  map a := SSet.π₀.mk a

/-- Every original enriched functor acts by its unchanged native component map. -/
def componentFunctor {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    componentObjects C ⥤ componentObjects D where
  obj x := F.obj x
  map {x y} a := SSet.mapπ₀ (F.map x y) a
  map_id x := by
    change SSet.π₀.mk ((F.map x x).app (op ⦋0⦌)
        ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit)) = _
    exact congrArg SSet.π₀.mk (congrFun (NatTrans.congr_app (F.map_id x) (op ⦋0⦌)) PUnit.unit)
  map_comp {x y z} a b := by
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    change SSet.π₀.mk ((F.map x z).app (op ⦋0⦌)
        ((C.enriched.comp x y z).app (op ⦋0⦌) (a, b))) = _
    exact congrArg SSet.π₀.mk
      (congrFun (NatTrans.congr_app (F.map_comp x y z) (op ⦋0⦌)) (a, b))

/-- The component functor for an original identity functor is the full identity. -/
theorem componentFunctor_id (C : SimplicialCat.{u, u}) :
    componentFunctor (𝟙 C) = 𝟭 (componentObjects C) := by
  refine Functor.hext (F := componentFunctor (𝟙 C))
    (G := 𝟭 (componentObjects C)) (fun _ ↦ rfl) ?_
  intro x y a
  exact heq_of_eq (SSet.mapπ₀_id_apply a)

/-- The component functor for an original composite is the full composite functor. -/
theorem componentFunctor_comp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E) :
    componentFunctor (F ≫ G) = componentFunctor F ⋙ componentFunctor G := by
  refine Functor.hext (F := componentFunctor (F ≫ G))
    (G := componentFunctor F ⋙ componentFunctor G) (fun _ ↦ rfl) ?_
  intro x y a
  exact heq_of_eq (SSet.mapπ₀_comp_apply (F.map x y) (G.map (F.obj x) (F.obj y)) a)

end
end DaggerOriginalSimplicialPiZeroCategory
