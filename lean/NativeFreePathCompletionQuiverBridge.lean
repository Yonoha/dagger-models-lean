import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory

/-! The categorical completion of native free paths is the native quiver free groupoid. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeFreePathCompletionQuiverBridge
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def pathUnit : Paths V ⥤ Quiver.FreeGroupoid V := Paths.lift (Quiver.FreeGroupoid.of V)

def toQuiver : FreeGroupoid (Paths V) ⥤ Quiver.FreeGroupoid V :=
  FreeGroupoid.lift (pathUnit V)

def fromQuiver : Quiver.FreeGroupoid V ⥤ FreeGroupoid (Paths V) :=
  Quiver.FreeGroupoid.lift ((Paths.of V) ⋙q (FreeGroupoid.of (Paths V)).toPrefunctor)

theorem categorical_unit_square : FreeGroupoid.of (Paths V) ⋙ toQuiver V = pathUnit V :=
  FreeGroupoid.lift_spec _

theorem quiver_unit_square :
    Quiver.FreeGroupoid.of V ⋙q (fromQuiver V).toPrefunctor =
      Paths.of V ⋙q (FreeGroupoid.of (Paths V)).toPrefunctor :=
  Quiver.FreeGroupoid.lift_spec _

theorem path_unit_square : pathUnit V ⋙ fromQuiver V = FreeGroupoid.of (Paths V) := by
  refine Paths.ext_functor (F := pathUnit V ⋙ fromQuiver V)
    (G := FreeGroupoid.of (Paths V)) rfl ?_
  intro a b e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have h := Prefunctor.congr_hom (quiver_unit_square V) e
  simpa only [pathUnit, CategoryTheory.Functor.comp_map, Paths.lift_toPath] using h

theorem toQuiver_fromQuiver : toQuiver V ⋙ fromQuiver V = 𝟭 _ := by
  have h : FreeGroupoid.of (Paths V) ⋙ (toQuiver V ⋙ fromQuiver V) =
      FreeGroupoid.of (Paths V) := by
    rw [← CategoryTheory.Functor.assoc, categorical_unit_square, path_unit_square]
  exact (FreeGroupoid.lift_unique _ _ h).trans
    (FreeGroupoid.lift_unique (FreeGroupoid.of (Paths V)) (𝟭 _)
      (CategoryTheory.Functor.comp_id _)).symm

theorem fromQuiver_toQuiver : fromQuiver V ⋙ toQuiver V = 𝟭 _ := by
  have h : Quiver.FreeGroupoid.of V ⋙q (fromQuiver V ⋙ toQuiver V).toPrefunctor =
      Quiver.FreeGroupoid.of V := by
    rw [← CategoryTheory.Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc,
      quiver_unit_square, Prefunctor.comp_assoc]
    change Paths.of V ⋙q (FreeGroupoid.of (Paths V) ⋙ toQuiver V).toPrefunctor = _
    rw [categorical_unit_square]
    exact Paths.lift_spec _
  exact (Quiver.FreeGroupoid.lift_unique _ _ h).trans
    (Quiver.FreeGroupoid.lift_unique (Quiver.FreeGroupoid.of V) (𝟭 _) (by rfl)).symm

end
end DaggerNativeFreePathCompletionQuiverBridge
