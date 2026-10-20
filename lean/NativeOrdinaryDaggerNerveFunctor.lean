import NativeOrdinaryDaggerNerveLift

/-! The SAME ordinary nerve map of every dagger-preserving ordinary functor. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalNerveOppositeMap DaggerNativeOrdinaryDaggerNerve
open DaggerNativeOrdinaryDaggerNerveLift
universe u
namespace DaggerNativeOrdinaryDaggerNerveFunctor
noncomputable section
variable {A B : Type u} [Category.{u} A] [Category.{u} B]
variable [DaggerCategory A] [DaggerCategory B]

/-- The original ordinary nerve map preserves reversed chains with the original daggers. -/
def map (F : A ⥤ B)
    (hF : ∀ {x y : A} (f : x ⟶ y),
      F.map (DaggerCategory.dagger f) = DaggerCategory.dagger (F.map f)) :
    daggerNerve A ⟶ daggerNerve B where
  hom := nerveMap F
  comm := by
    apply NatTrans.ext
    funext q G
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact (hF (((reverseDiagram G).map f).unop)).symm

/-- The entire underlying simplicial map is exactly the original ordinary nerve map. -/
theorem map_hom (F : A ⥤ B)
    (hF : ∀ {x y : A} (f : x ⟶ y),
      F.map (DaggerCategory.dagger f) = DaggerCategory.dagger (F.map f)) :
    (map F hF).hom = nerveMap F := rfl

end
end DaggerNativeOrdinaryDaggerNerveFunctor
