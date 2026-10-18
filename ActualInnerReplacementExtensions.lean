import ActualInnerAnodyneRigidification
import NativeInnerJoyalMappingWeak

/-! Original inner-horn replacement: weak rigidified Homs and extensions to EVERY quasi-category. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerNativeInnerHornFactorization
open scoped Simplicial SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerReplacementExtensions
noncomputable section

theorem unit_hom_anodyne (X : SSet.{u}) (a b : (rigidification.obj X).Obj) :
    SSet.anodyneExtensions ((rigidification.map (unit.app X)).map a b) :=
  DaggerActualInnerAnodyneRigidification.hom_anodyne _ (unit_innerAnodyne X) a b

theorem unit_hom_weak (X : SSet.{u}) (a b : (rigidification.obj X).Obj) :
    WeakEquivalence ((rigidification.map (unit.app X)).map a b) :=
  DaggerActualInnerAnodyneRigidification.hom_weak _ (unit_innerAnodyne X) a b

theorem unit_object_bijective (X : SSet.{u}) :
    Function.Bijective (rigidification.map (unit.app X)).obj :=
  DaggerActualInnerAnodyneRigidification.object_bijective _ (unit_innerAnodyne X)

theorem exists_extension {A X : SSet.{u}} [X.Quasicategory] (f : A ⟶ X) :
    ∃ g : replacement.obj A ⟶ X, unit.app A ≫ g = f := by
  have hl := unit_innerAnodyne A (terminal.from X)
    ((quasicategory_iff_inner_terminal (terminal.from X) terminalIsTerminal).1 inferInstance)
  let sq : CommSq f (unit.app A) (terminal.from X) (terminal.from (replacement.obj A)) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  have : sq.HasLift := hl.sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left⟩

theorem exists_retraction (X : SSet.{u}) [X.Quasicategory] :
    ∃ r : replacement.obj X ⟶ X, unit.app X ≫ r = 𝟙 X :=
  exists_extension (𝟙 X)

def extension {X : SSet.{u}} (r : replacement.obj X ⟶ X) {A : SSet.{u}}
    (f : A ⟶ X) : replacement.obj A ⟶ X := replacement.map f ≫ r

theorem unit_extension {X : SSet.{u}} (r : replacement.obj X ⟶ X)
    (hr : unit.app X ≫ r = 𝟙 X) {A : SSet.{u}} (f : A ⟶ X) :
    unit.app A ≫ extension r f = f := by
  unfold extension
  rw [← Category.assoc, ← unit.naturality f]
  change (f ≫ unit.app X) ≫ r = f
  rw [Category.assoc, hr, Category.comp_id]

theorem extension_naturality {X : SSet.{u}} (r : replacement.obj X ⟶ X)
    {A B : SSet.{u}} (f : A ⟶ B) (g : B ⟶ X) :
    replacement.map f ≫ extension r g = extension r (f ≫ g) := by
  unfold extension
  rw [Functor.map_comp, Category.assoc]

end
end DaggerActualInnerReplacementExtensions
