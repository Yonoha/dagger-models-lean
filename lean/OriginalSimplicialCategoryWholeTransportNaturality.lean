import OriginalSimplicialCategoryWholeBarFibreTransport

/-!
# Original whole Hom transport is natural for every original enriched functor

Keep the actual object map on all source and endpoint objects and the actual
Hom maps in every degree. Native coproduct reindexing retains the entire
original family. Naturality applies in particular to the actual localization.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeBarFibreFunctor
open DaggerOriginalSimplicialCategoryWholeHomTransport
universe u
namespace DaggerOriginalSimplicialCategoryWholeTransportNaturality
noncomputable section

/-- Every original enriched functor sends the original vertex point to its actual image point. -/
theorem vertexPoint_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    vertexPoint C a ≫ F.map x y = vertexPoint D ((F.map x y).app (op ⦋0⦌) a) := by
  apply (SSet.unitHomEquiv (D.enriched.Hom (F.obj x) (F.obj y))).injective
  change (F.map x y).app (op ⦋0⦌) ((vertexPoint C a).app (op ⦋0⦌) PUnit.unit) =
    (vertexPoint D ((F.map x y).app (op ⦋0⦌) a)).app (op ⦋0⦌) PUnit.unit
  rw [vertexPoint_zero, vertexPoint_zero]

/-- Every original enriched functor preserves original vertex precomposition on full Homs. -/
theorem precomposeVertex_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    F.map y z ≫ precomposeVertex D ((F.map x y).app (op ⦋0⦌) a) (F.obj z) =
      precomposeVertex C a z ≫ F.map x z := by
  apply NatTrans.ext
  funext n b
  change (precomposeVertex D ((F.map x y).app (op ⦋0⦌) a) (F.obj z)).app n
      ((F.map y z).app n b) = (F.map x z).app n ((precomposeVertex C a z).app n b)
  rw [precomposeVertex_apply, precomposeVertex_apply]
  have hp := congrFun (NatTrans.congr_app (vertexPoint_natural F a) n) PUnit.unit
  change (F.map x y).app n ((vertexPoint C a).app n PUnit.unit) =
    (vertexPoint D ((F.map x y).app (op ⦋0⦌) a)).app n PUnit.unit at hp
  have hc := congrFun (NatTrans.congr_app (F.map_comp x y z) n)
    ((vertexPoint C a).app n PUnit.unit, b)
  change _ = (D.enriched.comp (F.obj x) (F.obj y) (F.obj z)).app n
    ((F.map x y).app n ((vertexPoint C a).app n PUnit.unit), (F.map y z).app n b) at hc
  rw [hp] at hc
  exact hc.symm

/-- The actual object map and all original Hom maps commute with the entire Hom-sum transport. -/
theorem wholeHomPrecompose_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    {x y : C.Obj} (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    originalHomSumMap F y ≫ wholeHomPrecompose D ((F.map x y).app (op ⦋0⦌) a) =
      wholeHomPrecompose C a ≫ originalHomSumMap F x := by
  apply Sigma.hom_ext
  intro z
  change Sigma.ι (fun z ↦ C.enriched.Hom y z) z ≫
      (Limits.Sigma.map' F.obj (F.map y) ≫
        Limits.Sigma.map (fun t ↦ precomposeVertex D ((F.map x y).app (op ⦋0⦌) a) t)) =
    Sigma.ι (fun z ↦ C.enriched.Hom y z) z ≫
      (Limits.Sigma.map (fun z ↦ precomposeVertex C a z) ≫
        Limits.Sigma.map' F.obj (F.map x))
  rw [← Category.assoc, Sigma.ι_comp_map', Category.assoc, Sigma.ι_map,
    ← Category.assoc, precomposeVertex_natural, Category.assoc,
    ← Sigma.ι_comp_map', ← Category.assoc, ← Category.assoc, Sigma.ι_map]

end
end DaggerOriginalSimplicialCategoryWholeTransportNaturality
