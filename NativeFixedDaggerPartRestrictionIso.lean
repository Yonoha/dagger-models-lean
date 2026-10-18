import NativeFixedDaggerIsomorphismPart
import NativeDaggerRestrictionInclusion
import NativeDaggerLabelTransport

/-! Restricting to arbitrary original object labels commutes with the SAME isomorphism part.
Both directions are identity on every underlying simplex; repeated labels are allowed.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerNativeDaggerObjectRestriction DaggerNativeDaggerRestrictionInclusion
open DaggerNativeDaggerLabelTransport
universe u
namespace DaggerNativeFixedDaggerPartRestrictionIso
noncomputable section

private abbrev P := DaggerActualDaggerIsomorphismComponentPart.part
private abbrev FP {O : Type u} (C : FixedDaggerCategory O) : FixedDaggerCategory O :=
  DaggerNativeFixedDaggerIsomorphismPart.part C

def hom {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) :
    restriction (P D) θ ⟶ FP (restriction D θ) where
  underlying :=
    { map := fun i j ↦
        { app := fun q s ↦ ⟨s.val, (part_mem_iff D θ i j q s.val).mpr s.property⟩
          naturality := by intro q r f; funext s; rfl }
      map_id := fun i ↦ by
        apply NatTrans.ext
        funext q s
        apply Subtype.ext
        rfl
      map_comp := fun i j k ↦ by
        apply NatTrans.ext
        funext q s
        apply Subtype.ext
        rfl }
  map_dagger := fun i j ↦ by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    rfl

def inv {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) :
    FP (restriction D θ) ⟶ restriction (P D) θ where
  underlying :=
    { map := fun i j ↦
        (DaggerActualDaggerIsomorphismComponentMaps.map (inclusion D θ)).map i j
      map_id := fun i ↦
        (DaggerActualDaggerIsomorphismComponentMaps.map (inclusion D θ)).map_id i
      map_comp := fun i j k ↦
        (DaggerActualDaggerIsomorphismComponentMaps.map (inclusion D θ)).map_comp i j k }
  map_dagger := (DaggerActualDaggerIsomorphismComponentMaps.map (inclusion D θ)).map_dagger

def comparisonIso {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj) :
    restriction (P D) θ ≅ FP (restriction D θ) where
  hom := hom D θ
  inv := inv D θ
  hom_inv_id := by
    apply fixedDaggerHom_ext
    apply fixedHom_ext
    intro i j
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply fixedDaggerHom_ext
    apply fixedHom_ext
    intro i j
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    rfl

theorem hom_raw {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj)
    (i j : O) (q : SimplexCategoryᵒᵖ)
    (s : ((restriction (P D) θ).underlying.enriched.Hom i j).obj q) :
    (((comparisonIso D θ).hom.underlying.map i j).app q s).val = s.val := rfl

theorem naturality {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) (ψ : O → E.Obj) (h : F.obj ∘ θ = ψ) :
    mapAlong (DaggerActualDaggerIsomorphismComponentMaps.map F) θ ψ h ≫
        (comparisonIso E ψ).hom =
      (comparisonIso D θ).hom ≫
        DaggerNativeFixedDaggerIsomorphismPart.map (mapAlong F θ ψ h) := by
  subst ψ
  apply fixedDaggerHom_ext
  apply fixedHom_ext
  intro i j
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  rfl

end
end DaggerNativeFixedDaggerPartRestrictionIso
