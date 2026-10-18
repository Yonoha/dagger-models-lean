import OriginalConnectedCotensorBarRows

/-! Exact connected mapping rows inherit the original cotensor pi0 Kan descent inputs. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalClosed HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalCotensorPrecompositionWeak
open DaggerOriginalNerveRowsPiZero DaggerOriginalBarRowsPiZero
open DaggerOriginalConnectedCotensorBaseRows DaggerOriginalConnectedCotensorBarRows
open DaggerOriginalConnectedCotensorRowIso DaggerOriginalCotensorPiZeroGroupoid
open DaggerOriginalAmbientDaggerPiZeroGroupoid OriginalOrdinaryLocalKanReplacement
open DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalConnectedMappingRowPiZero
noncomputable section

def mappingBaseComponents (K : SSet.{u}) (C : SimplicialCat.{u, u}) : SSet.{u} :=
  baseRows C ⋙ ihom K ⋙ SSet.π₀Functor

def mappingBarComponents (K : SSet.{u}) (C : SimplicialCat.{u, u}) (z : C.Obj) : SSet.{u} :=
  barRows C z ⋙ ihom K ⋙ SSet.π₀Functor

def mappingComponentProjection (K : SSet.{u}) (C : SimplicialCat.{u, u}) (z : C.Obj) :
    mappingBarComponents K C z ⟶ mappingBaseComponents K C where
  app n := SSet.mapπ₀ ((ihom K).map (rowProjection C z n.unop.len))
  naturality n m α := by
    obtain ⟨n⟩ := n
    obtain ⟨m⟩ := m
    induction n using SimplexCategory.rec with | _ n =>
      induction m using SimplexCategory.rec with | _ m =>
        have h := congrArg (fun f ↦ (ihom K ⋙ SSet.π₀Functor).map f)
          (rowProjection_horizontal C z α.unop)
        simpa only [Functor.map_comp] using h

def baseComponentsIhomIso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) :
    componentRows (originalCotensor K C) ≅ mappingBaseComponents K C :=
  ((Functor.whiskeringRight _ _ _).obj SSet.π₀Functor).mapIso (baseRowsIhomIso K v C)

def barComponentsIhomIso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (z : C.Obj) :
    barComponentRows (originalCotensor K C) z ≅ mappingBarComponents K C z :=
  ((Functor.whiskeringRight _ _ _).obj SSet.π₀Functor).mapIso (barRowsIhomIso K v C z)

theorem component_projection_square (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (z : C.Obj) :
    (barComponentsIhomIso K v C z).hom ≫ mappingComponentProjection K C z =
      componentRowProjection (originalCotensor K C) z ≫ (baseComponentsIhomIso K v C).hom := by
  apply NatTrans.ext
  funext n q
  change SSet.mapπ₀ ((ihom K).map (rowProjection C z n.unop.len))
      (SSet.mapπ₀ (barRowIhomIso K v C z n.unop.len).hom q) =
    SSet.mapπ₀ (baseRowIhomIso K v C n.unop.len).hom
      (SSet.mapπ₀ (rowProjection (originalCotensor K C) z n.unop.len) q)
  rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply,
    ← barRowIhomMap_eq_iso, ← baseRowIhomMap_eq_iso, row_projection_ihom_square]

theorem mapping_base_components_kan (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) :
    (mappingBaseComponents K C).KanComplex := by
  have := cotensor_base_rows_kan K C hC hH
  exact isFibrant_of_fibration (baseComponentsIhomIso K v C).inv

theorem mapping_bar_components_kan (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (z : C.Obj) :
    (mappingBarComponents K C z).KanComplex := by
  have := cotensor_bar_rows_kan K C hC hH z
  exact isFibrant_of_fibration (barComponentsIhomIso K v C z).inv

theorem mapping_projection_fibration (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C)
    (hH : ∀ x y : C.Obj, (C.enriched.Hom x y).KanComplex) (z : C.Obj) :
    Fibration (mappingComponentProjection K C z) := by
  have hp := cotensor_pi_zero_projection_fibration K C hC hH z
  let a : Arrow.mk (componentRowProjection (originalCotensor K C) z) ≅
      Arrow.mk (mappingComponentProjection K C z) :=
    Arrow.isoMk (barComponentsIhomIso K v C z) (baseComponentsIhomIso K v C)
      (component_projection_square K v C z)
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff a).mp
      ((HomotopicalAlgebra.fibration_iff _).mp hp))

theorem replacement_mapping_descent_inputs (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) :
    (mappingBaseComponents K (replacement.obj C)).KanComplex ∧
      ∀ z : (replacement.obj C).Obj,
        (mappingBarComponents K (replacement.obj C) z).KanComplex ∧
          Fibration (mappingComponentProjection K (replacement.obj C) z) := by
  have h := (replacement_groupoid_iff C).mp hC
  have hh := replacement_locallyKan C
  exact ⟨mapping_base_components_kan K v _ h hh, fun z ↦
    ⟨mapping_bar_components_kan K v _ h hh z, mapping_projection_fibration K v _ h hh z⟩⟩

end
end DaggerOriginalConnectedMappingRowPiZero
