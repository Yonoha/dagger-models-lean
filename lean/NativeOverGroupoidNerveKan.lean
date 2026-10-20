import NativeGroupoidNerveKan

/-! The actual over-category of a groupoid has a unique arrow between any two objects. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeOverGroupoidNerveKan
noncomputable section

def overHom (G : Type u) [Groupoid.{u} G] (z : G) (X Y : Over z) : X ⟶ Y :=
  Over.homMk (X.hom ≫ inv Y.hom) (by simp)

theorem overHom_unique (G : Type u) [Groupoid.{u} G] (z : G)
    {X Y : Over z} (f g : X ⟶ Y) : f = g := by
  apply CostructuredArrow.ext
  apply (cancel_mono Y.hom).mp
  exact (Over.w f).trans (Over.w g).symm

def overGroupoid (G : Type u) [Groupoid.{u} G] (z : G) : Groupoid.{u} (Over z) :=
  Groupoid.ofHomUnique (fun {X Y} ↦
    { default := overHom G z X Y
      uniq := fun f ↦ overHom_unique G z f (overHom G z X Y) })

theorem overGroupoid_toCategory (G : Type u) [Groupoid.{u} G] (z : G) :
    (overGroupoid G z).toCategory = (inferInstance : Category.{u} (Over z)) := rfl

theorem over_nerve_kan (G : Type u) [Groupoid.{u} G] (z : G) :
    (nerve (Over z)).KanComplex := by
  letI := overGroupoid G z
  exact DaggerNativeGroupoidNerveKan.nerve_kan (Over z)

end
end DaggerNativeOverGroupoidNerveKan
