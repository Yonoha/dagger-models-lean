import OriginalLeftMappingFunctoriality
import TopCatModelCategory.ModelCategorySSet

/-!
# Actual mapping-space equivalences imply native homotopy full faithfulness

The exact natural component-to-Hom comparison transports bijectivity of the
actual left mapping-space component maps to the original native Hom maps.
In particular, weak equivalences of these actual Kan mapping spaces give a
fully faithful original homotopy functor. This closes the one-categorical
consequence of mapping-space full faithfulness, without replacing the higher
mapping-space requirement by this weaker consequence.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalInnerHornFillers DaggerOriginalQuasicategoryLeftMappingSpace
open DaggerOriginalLeftMappingPiZeroHom DaggerOriginalLeftMappingFunctoriality

universe u

namespace DaggerOriginalLeftMappingFullFaithfulness

noncomputable section

/-- Bijectivity on actual mapping-space components implies bijectivity on original native Hom.
-/
theorem homotopyMap_on_vertices_bijective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y) (x y : X.obj (op ⦋0⦌))
    (hπ₀ : Function.Bijective (SSet.mapπ₀ (leftMappingMap f x y))) :
    Function.Bijective ((SSet.hoFunctor.map f).toFunctor.map
      (X := SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) x)
      (Y := SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y)) := by
  constructor
  · intro p q hpq
    obtain ⟨a, rfl⟩ := piZeroToHom_surjective hX x y p
    obtain ⟨b, rfl⟩ := piZeroToHom_surjective hX x y q
    apply congrArg (piZeroToHom X x y)
    apply hπ₀.1
    apply piZeroToHom_injective hY (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)
    rw [piZeroToHom_naturality, piZeroToHom_naturality]
    exact hpq
  · intro g
    obtain ⟨d, hd⟩ := piZeroToHom_surjective hY
      (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) g
    obtain ⟨c, hc⟩ := hπ₀.2 d
    refine ⟨piZeroToHom X x y c, ?_⟩
    rw [← piZeroToHom_naturality, hc, hd]

/-- The actual mapping component maps give faithfulness of the original homotopy functor. -/
theorem homotopyMap_faithful_of_mapping_piZero {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (hπ₀ : ∀ x y : X.obj (op ⦋0⦌),
      Function.Bijective (SSet.mapπ₀ (leftMappingMap f x y))) :
    (SSet.hoFunctor.map f).toFunctor.Faithful where
  map_injective {a b} p q h := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    exact (homotopyMap_on_vertices_bijective f hX hY x y (hπ₀ x y)).1 h

/-- The actual mapping component maps give fullness of the original homotopy functor. -/
theorem homotopyMap_full_of_mapping_piZero {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (hπ₀ : ∀ x y : X.obj (op ⦋0⦌),
      Function.Bijective (SSet.mapπ₀ (leftMappingMap f x y))) :
    (SSet.hoFunctor.map f).toFunctor.Full where
  map_surjective {a b} g := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    exact (homotopyMap_on_vertices_bijective f hX hY x y (hπ₀ x y)).2 g

/-- Weak equivalence of the actual mapping spaces gives bijectivity on their actual components.
-/
theorem mapping_piZero_bijective_of_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y) (x y : X.obj (op ⦋0⦌))
    (hmap : WeakEquivalence (leftMappingMap f x y)) :
    Function.Bijective (SSet.mapπ₀ (leftMappingMap f x y)) := by
  haveI : (leftMappingSpace X x y).KanComplex := leftMappingSpace_kan hX x y
  haveI : (leftMappingSpace Y (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)).KanComplex :=
    leftMappingSpace_kan hY _ _
  haveI := hmap
  exact ((SSet.weakEquivalence_iff_kanComplexW _).1 hmap).bijective_mapπ₀

/-- Weak equivalences of actual original left mapping spaces give native homotopy faithfulness.
-/
theorem homotopyMap_faithful_of_mapping_weakEquivalences {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (hmap : ∀ x y : X.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f x y)) :
    (SSet.hoFunctor.map f).toFunctor.Faithful :=
  homotopyMap_faithful_of_mapping_piZero f hX hY
    (fun x y ↦ mapping_piZero_bijective_of_weakEquivalence f hX hY x y (hmap x y))

/-- Weak equivalences of actual original left mapping spaces give native homotopy fullness. -/
theorem homotopyMap_full_of_mapping_weakEquivalences {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (hmap : ∀ x y : X.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f x y)) :
    (SSet.hoFunctor.map f).toFunctor.Full :=
  homotopyMap_full_of_mapping_piZero f hX hY
    (fun x y ↦ mapping_piZero_bijective_of_weakEquivalence f hX hY x y (hmap x y))

end

end DaggerOriginalLeftMappingFullFaithfulness
