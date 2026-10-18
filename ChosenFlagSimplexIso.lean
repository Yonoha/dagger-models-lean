import ChosenNecklaceFlagIso
import ChosenFlagFunctor
import ChosenNecklaceSingleThickening

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

/-- Actual flags on the standard simplex, with full enriched inverses and all Hom endpoints. -/
def flagSimplexIso (n : ℕ) : E (Δ[n] : SSet.{u}) ≅ T.obj ⦋n⦌ :=
  (flagCategoryFunctor.mapIso (singleIso n)).symm ≪≫
    necklaceFlagIso (single n) ≪≫ singleNCIso n

theorem singleIso_inv_vertices (n : ℕ) (x : (Δ[n] : SSet.{u}).obj (op ⦋0⦌)) :
    (single n).verticesEquiv ((singleIso n).inv.app _ x) =
      ULift.up (SSet.stdSimplex.obj₀Equiv.{u} x) := by
  apply ULift.ext
  have h := singleIso_vertex n ((singleIso n).inv.app _ x)
  have he := congrFun (NatTrans.congr_app (singleIso.{u} n).inv_hom_id (op ⦋0⦌)) x
  change ((single n).verticesEquiv ((singleIso n).inv.app _ x)).down = _
  exact h.symm.trans (congrArg SSet.stdSimplex.obj₀Equiv.{u} he)

theorem flagSimplexIso_hom_obj (n : ℕ) (x : (Δ[n] : SSet.{u}).obj (op ⦋0⦌)) :
    (flagSimplexIso n).hom.obj x = ⟨ULift.up (SSet.stdSimplex.obj₀Equiv.{u} x)⟩ := by
  change (SimplicialThickening.mk
    ((single n).verticesEquiv ((singleIso n).inv.app _ x))) = _
  exact congrArg SimplicialThickening.mk (singleIso_inv_vertices n x)

theorem flagSimplexIso_inv_obj (n : ℕ) (a : (T.{u}.obj ⦋n⦌).Obj) :
    (flagSimplexIso n).inv.obj a = SSet.stdSimplex.obj₀Equiv.{u}.symm a.as.down := by
  apply SSet.stdSimplex.obj₀Equiv.{u}.injective
  change SSet.stdSimplex.obj₀Equiv.{u}
    ((singleIso n).hom.app _ ((single n).verticesEquiv.symm a.as)) = _
  rw [singleIso_vertex, Equiv.apply_symm_apply]
  exact (SSet.stdSimplex.obj₀Equiv.{u}.apply_symm_apply a.as.down).symm

def simplexVertexMap {P : NecklaceCode} {n : ℕ} (f : toSSet.{u} P ⟶ Δ[n]) :
    Vertices.{u} P → ULift.{u} (Fin (n + 1)) :=
  fun v ↦ ULift.up (SSet.stdSimplex.obj₀Equiv.{u} (f.app _ (P.verticesEquiv.symm v)))

/-- Full Hom map on every actual raw flag, retaining the original simplex vertex map. -/
theorem flagSimplexIso_hom_raw_I (n : ℕ) {x y : (Δ[n] : SSet.{u}).obj (op ⦋0⦌)}
    (P : NecklacesOver (Δ[n] : SSet.{u}) x y) (q : SimplexCategoryᵒᵖ)
    (F : NecklaceCode.Flag.{u} P.code q.unop.len) (i : Fin (q.unop.len + 1)) :
    ((((flagSimplexIso n).hom.map x y).app q (Quot.mk _ ⟨P, F⟩)).obj i).I =
      simplexVertexMap P.map '' F.chain i := by
  change mapVertices (P.map ≫ (singleIso n).inv) '' F.chain i = _
  congr 1
  funext v
  exact singleIso_inv_vertices n (P.map.app _ (P.code.verticesEquiv.symm v))

end

end DaggerChosenRigidificationNecklace
