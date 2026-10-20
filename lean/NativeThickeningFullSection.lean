import NativeThickeningFullPaths
import NativeOrdinalRigidificationNaturality

/-! A levelwise enriched section of the SAME original ordinal projection. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualOrdinalRigidificationComparison
open DaggerNativeOrdinalRigidificationNaturality DaggerNativeThickeningFullPaths
universe u
namespace DaggerNativeThickeningFullSection
noncomputable section

local instance (n : SimplexCategory) : EnrichedCategory SSet.{u} (ordinal n) :=
  DaggerUnitaryDiscrete.ordinaryEnriched _

/-- Full paths give a genuine enriched functor, including all original composition laws. -/
def fullSection (n : SimplexCategory) :
    constant (ordinal.{u} n) ⟶ cosimplicialThickening.obj n where
  obj i := ⟨i⟩
  map i j :=
    { app := fun q f ↦ (CategoryTheory.Functor.const (Fin (q.unop.len + 1))).obj
        (fullPath i j (leOfHom f))
      naturality := by intros; rfl }
  map_id i := by
    ext q p
    exact CategoryTheory.Functor.ext
      (fun _ ↦ SimplicialThickening.Path.ext (Set.Icc_self i))
  map_comp i j k := by
    ext q p
    exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext
      (fullPath_union i j k (leOfHom p.1) (leOfHom p.2)).symm)

/-- The projection-section composite is the exact identity on the constant ordinal. -/
theorem fullSection_projection (n : SimplexCategory) :
    fullSection.{u} n ≫ thickeningProjection n.len = 𝟙 (constant (ordinal.{u} n)) := by
  apply EnrichedFunctor.ext SSet
    (F := fullSection n ≫ thickeningProjection n.len)
    (G := 𝟙 (constant (ordinal.{u} n))) (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply NatTrans.ext
  funext q f
  change (_ : i ⟶ j) = _
  exact Subsingleton.elim _ _

/-- Every original ordinal object is retained, without any assumption on its image later. -/
theorem fullSection_obj (n : SimplexCategory) (i : ordinal.{u} n) :
    (fullSection n).obj i = (⟨i⟩ : SimplicialThickening (ordinal.{u} n)) := rfl

end
end DaggerNativeThickeningFullSection
