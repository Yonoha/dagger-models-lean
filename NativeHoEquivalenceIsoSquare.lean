import NativeHoOppositeEquivalence

/-!
# Equivalence tests in exact commuting isomorphism squares

Cancel the native ordinary category equivalences on the two sides of the square.
The homotopy-category application retains the whole original simplicial-set maps.
-/
set_option autoImplicit false
open CategoryTheory
universe v u
namespace DaggerNativeHoEquivalenceIsoSquare

/-- Native category equivalence is invariant across the exact strict commuting iso square. -/
theorem cat_equivalence_iff_of_iso_square {X Y X' Y' : Cat.{v, u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : f ≫ eY.hom = eX.hom ≫ g) :
    f.toFunctor.IsEquivalence ↔ g.toFunctor.IsEquivalence := by
  letI : eX.hom.toFunctor.IsEquivalence :=
    show (Cat.equivOfIso eX).functor.IsEquivalence by infer_instance
  letI : eY.hom.toFunctor.IsEquivalence :=
    show (Cat.equivOfIso eY).functor.IsEquivalence by infer_instance
  have hn : f.toFunctor ⋙ eY.hom.toFunctor = eX.hom.toFunctor ⋙ g.toFunctor :=
    congrArg (fun k ↦ k.toFunctor) h
  constructor
  · intro hf
    letI : f.toFunctor.IsEquivalence := hf
    letI : (eX.hom.toFunctor ⋙ g.toFunctor).IsEquivalence := by
      rw [← hn]
      infer_instance
    exact CategoryTheory.Functor.isEquivalence_of_comp_left eX.hom.toFunctor g.toFunctor
  · intro hg
    letI : g.toFunctor.IsEquivalence := hg
    letI : (f.toFunctor ⋙ eY.hom.toFunctor).IsEquivalence := by
      rw [hn]
      infer_instance
    exact CategoryTheory.Functor.isEquivalence_of_comp_right f.toFunctor eY.hom.toFunctor

/-- Native ho preserves the exact square and both of its native isomorphisms. -/
theorem ho_equivalence_iff_of_iso_square {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : f ≫ eY.hom = eX.hom ≫ g) :
    (SSet.hoFunctor.map f).toFunctor.IsEquivalence ↔
      (SSet.hoFunctor.map g).toFunctor.IsEquivalence := by
  apply cat_equivalence_iff_of_iso_square (SSet.hoFunctor.map f) (SSet.hoFunctor.map g)
    (SSet.hoFunctor.mapIso eX) (SSet.hoFunctor.mapIso eY)
  change SSet.hoFunctor.map f ≫ SSet.hoFunctor.map eY.hom =
    SSet.hoFunctor.map eX.hom ≫ SSet.hoFunctor.map g
  rw [← SSet.hoFunctor.map_comp, ← SSet.hoFunctor.map_comp, h]

end DaggerNativeHoEquivalenceIsoSquare
