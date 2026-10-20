import NativeGroupoidPalindromicSection

/-! The entire palindromic section is natural in ALL original groupoid functors. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerNativeGroupoidChainExtension DaggerNativeGroupoidPalindromicSection
open DaggerNativeRealEdgewiseSSet
universe u
namespace DaggerNativeGroupoidPalindromicNaturality
noncomputable section
variable {C D : Type u} [Groupoid.{u} C] [Groupoid.{u} D]

/-- Every original functor maps the SAME inverse-chain arrows to the SAME arrows. -/
theorem bridge_postcomp {n : ℕ} (F : Fin (n + 1) ⥤ C) (P : C ⥤ D)
    (i j : Fin (n + 1)) : bridge (F ⋙ P) i j = P.map (bridge F i j) := by
  simp only [bridge, CategoryTheory.Functor.comp_map, P.map_comp, P.map_inv]

/-- Extend the original chain before or after applying the original groupoid functor. -/
theorem ofVertices_postcomp {n m : ℕ} (F : Fin (n + 1) ⥤ C) (P : C ⥤ D)
    (v : Fin (m + 1) → Fin (n + 1)) :
    ofVertices (F ⋙ P) v = ofVertices F v ⋙ P := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
    bridge_postcomp F P (v i) (v j)

/-- The WHOLE original simplicial section is natural, retaining every object function. -/
theorem section_naturality (P : C ⥤ D) :
    nerveMap P ≫ sectionMap D = sectionMap C ≫ edgewise.map (nerveMap P) := by
  apply NatTrans.ext
  funext n F
  exact ofVertices_postcomp F P (DaggerNativePalindromicVertexFold.vertex n.unop)

end
end DaggerNativeGroupoidPalindromicNaturality
