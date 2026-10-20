import IntervalCodiscrete
import ChosenNecklaceMapInclusion
import ChosenNecklaceSingleBead
import ChosenNecklacesOver

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerIntervalNecklaceCompletion

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

theorem singleIso_vertex_symm (n : ℕ) (k : Fin (n + 1)) :
    (singleIso.{u} n).hom.app _ ((single n).verticesEquiv.symm (ULift.up k)) =
      SSet.stdSimplex.obj₀Equiv.symm k := by
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [singleIso_hom]
  exact (single n).inclusion_vertex (ULift.up k)

theorem singleIso_inv_vertex (n : ℕ) (k : Fin (n + 1)) :
    (singleIso.{u} n).inv.app _ (SSet.stdSimplex.obj₀Equiv.symm k) =
      (single n).verticesEquiv.symm (ULift.up k) := by
  rw [← singleIso_vertex_symm]
  exact congrFun (NatTrans.congr_app (singleIso n).hom_inv_id (op ⦋0⦌)) _

theorem completeMap_naturality {T U : NecklaceCode}
    (g : T.toSSet ⟶ U.toSSet) (p : T.toSSet ⟶ E.{u}) (q : U.toSSet ⟶ E.{u})
    (hg : g ≫ q = p) :
    SSet.stdSimplex.map (SimplexCategory.Hom.mk (orderMap g) : ⦋T.len⦌ ⟶ ⦋U.len⦌) ≫
      completeMap U q =
      completeMap T p := by
  apply completeMap_unique T p
  rw [← Category.assoc, ← map_inclusion, Category.assoc, inclusion_completeMap, hg]

def inclusionToSingleMap (T : NecklaceCode) : T.toSSet ⟶ (single T.len).toSSet :=
  T.inclusion ≫ (singleIso T.len).inv

theorem inclusionToSingle_vertex (T : NecklaceCode) (k : Fin (T.len + 1)) :
    (inclusionToSingleMap.{u} T).app _ (T.verticesEquiv.symm (ULift.up k)) =
      (single T.len).verticesEquiv.symm (ULift.up k) := by
  have hv : T.inclusion.app _ (T.verticesEquiv.symm (ULift.up k)) =
      SSet.stdSimplex.obj₀Equiv.symm k := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    exact T.inclusion_vertex (ULift.up k)
  change (singleIso T.len).inv.app _ (T.inclusion.app _ _) = _
  rw [hv, singleIso_inv_vertex]

def inclusionToSingle (T : NecklaceCode) : NecklaceCode.Hom.{u} T (single T.len) where
  map := inclusionToSingleMap T
  first := inclusionToSingle_vertex T 0
  last := inclusionToSingle_vertex T (Fin.last T.len)

def completedMap {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U) :
    (single T.len).toSSet ⟶ (single U.len).toSSet :=
  (singleIso T.len).hom ≫
    SSet.stdSimplex.map (SimplexCategory.Hom.mk (orderMap f.map) : ⦋T.len⦌ ⟶ ⦋U.len⦌) ≫
      (singleIso U.len).inv

theorem completedMap_vertex {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U)
    (k : Fin (T.len + 1)) :
    (completedMap f).app _ ((single T.len).verticesEquiv.symm (ULift.up k)) =
      (single U.len).verticesEquiv.symm (ULift.up (orderMap f.map k)) := by
  change (singleIso U.len).inv.app _
    ((SSet.stdSimplex.map ((SimplexCategory.Hom.mk (orderMap f.map) : ⦋T.len⦌ ⟶ ⦋U.len⦌))).app _
      ((singleIso T.len).hom.app _ _)) = _
  rw [singleIso_vertex_symm]
  change (singleIso U.len).inv.app _
    (SSet.stdSimplex.obj₀Equiv.symm (orderMap f.map k)) = _
  exact singleIso_inv_vertex U.len (orderMap f.map k)

def completedHom {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U) :
    NecklaceCode.Hom.{u} (single T.len) (single U.len) where
  map := completedMap f
  first := by
    change (completedMap f).app _ ((single T.len).verticesEquiv.symm (ULift.up 0)) = _
    rw [completedMap_vertex, orderMap_first f]
    rfl
  last := by
    change (completedMap f).app _
      ((single T.len).verticesEquiv.symm (ULift.up (Fin.last T.len))) = _
    rw [completedMap_vertex, orderMap_last f]
    rfl

theorem inclusionToSingle_naturality {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U) :
    (inclusionToSingle T).map ≫ (completedHom f).map =
      f.map ≫ (inclusionToSingle U).map := by
  change (T.inclusion ≫ (singleIso T.len).inv) ≫
    ((singleIso T.len).hom ≫ _ ≫ (singleIso U.len).inv) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← map_inclusion]
  rfl

theorem completedHom_id (T : NecklaceCode) :
    completedHom (NecklaceCode.Hom.id T) = NecklaceCode.Hom.id (single T.len) := by
  apply NecklaceCode.Hom.ext
  apply NecklaceCode.hom_ext_vertices
  funext v
  change mapVertices (completedMap (NecklaceCode.Hom.id T)) v = mapVertices (𝟙 _) v
  rw [mapVertices_id]
  obtain ⟨k⟩ := v
  change (single T.len).verticesEquiv ((completedMap _).app _ _) = ULift.up k
  rw [completedMap_vertex]
  simp only [Equiv.apply_symm_apply]
  apply ULift.ext
  change (T.verticesEquiv (T.verticesEquiv.symm (ULift.up k))).down = k
  rw [T.verticesEquiv.apply_symm_apply]

theorem completedHom_comp {T U V : NecklaceCode}
    (f : NecklaceCode.Hom.{u} T U) (g : NecklaceCode.Hom.{u} U V) :
    completedHom (NecklaceCode.Hom.comp f g) =
      NecklaceCode.Hom.comp (completedHom f) (completedHom g) := by
  apply NecklaceCode.Hom.ext
  apply NecklaceCode.hom_ext_vertices
  funext v
  obtain ⟨k⟩ := v
  change (single V.len).verticesEquiv ((completedMap (NecklaceCode.Hom.comp f g)).app _ _) =
    (single V.len).verticesEquiv ((completedMap g).app _ ((completedMap f).app _ _))
  rw [completedMap_vertex]
  rw [completedMap_vertex, completedMap_vertex]
  apply congrArg ((single V.len).verticesEquiv ∘ (single V.len).verticesEquiv.symm)
  apply ULift.ext
  have h := congrFun (NecklaceCode.mapVertices_comp f.map g.map) (ULift.up k)
  exact congrArg ULift.down h

end

end DaggerIntervalNecklaceCompletion
