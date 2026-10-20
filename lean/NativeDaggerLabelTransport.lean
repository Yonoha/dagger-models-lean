import NativeDaggerObjectRestriction

/-! Restrict an original dagger map to specified labels with their equality witnessed explicitly. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerNativeDaggerObjectRestriction
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeDaggerLabelTransport
noncomputable section

def mapAlong {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) (ψ : O → E.Obj) (h : F.obj ∘ θ = ψ) :
    restriction D θ ⟶ restriction E ψ := by
  subst ψ
  exact DaggerNativeDaggerObjectRestriction.map F θ

theorem mapAlong_congr {O : Type u} {D E : DaggerSimplicialCat.{u, u}}
    {F G : D ⟶ E} (e : F = G) (θ : O → D.Obj) (ψ : O → E.Obj)
    (hF : F.obj ∘ θ = ψ) (hG : G.obj ∘ θ = ψ) :
    mapAlong F θ ψ hF = mapAlong G θ ψ hG := by
  subst G
  rfl

theorem mapAlong_refl {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) :
    mapAlong F θ (F.obj ∘ θ) rfl = DaggerNativeDaggerObjectRestriction.map F θ :=
  rfl

theorem mapAlong_id {O : Type u} (D : DaggerSimplicialCat.{u, u}) (θ : O → D.Obj)
    (h : (𝟙 D : D ⟶ D).obj ∘ θ = θ) :
    mapAlong (𝟙 D) θ θ h = 𝟙 (restriction D θ) :=
  DaggerNativeDaggerObjectRestriction.map_id D θ

theorem mapAlong_comp {O : Type u} {D E K : DaggerSimplicialCat.{u, u}}
    (F : D ⟶ E) (G : E ⟶ K) (θ : O → D.Obj) (ψ : O → E.Obj) (χ : O → K.Obj)
    (h : F.obj ∘ θ = ψ) (k : G.obj ∘ ψ = χ) (hk : (F ≫ G).obj ∘ θ = χ) :
    mapAlong (F ≫ G) θ χ hk = mapAlong F θ ψ h ≫ mapAlong G ψ χ k := by
  subst ψ
  subst χ
  exact DaggerNativeDaggerObjectRestriction.map_comp F G θ

theorem mapAlong_weak {O : Type u} {D E : DaggerSimplicialCat.{u, u}} (F : D ⟶ E)
    (θ : O → D.Obj) (ψ : O → E.Obj) (h : F.obj ∘ θ = ψ)
    (hF : ∀ x y : D.Obj, WeakEquivalence (F.map x y)) :
    WeakEquivalence (mapAlong F θ ψ h) := by
  subst ψ
  exact DaggerNativeDaggerObjectRestriction.map_weak F θ hF

end
end DaggerNativeDaggerLabelTransport
