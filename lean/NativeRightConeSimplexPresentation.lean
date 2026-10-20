import ActualGeneralRightConeMapping

/-! A literal cone map is the same whole simplex with the original constant face and last vertex. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerActualGeneralRightConeMapping
universe u
namespace DaggerNativeRightConeSimplexPresentation
noncomputable section
private theorem point_vertex {Y : SSet.{u}} (f : (Δ[0] : SSet.{u}) ⟶ Y)
    (z : (Δ[0] : SSet.{u}).obj (op ⦋0⦌)) : f.app _ z = SSet.yonedaEquiv f := by
  have hz : z = SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    omega
  rw [hz]
  rfl

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def simplexSpace : SSet.{u} where
  obj q := {f : (Δ[q.unop.len + 1] : SSet.{u}) ⟶ X //
    face q.unop.len ≫ f = SSet.const a ∧ lastVertex q.unop.len ≫ f = SSet.const b}
  map {_ _} α s := ⟨joinMap α.unop ≫ s.val, by
    constructor
    · rw [← Category.assoc, face_naturality, Category.assoc, s.property.1, SSet.comp_const]
    · rw [← Category.assoc, lastVertex_naturality, s.property.2]⟩
  map_id q := by
    funext s
    apply Subtype.ext
    change joinMap (𝟙 q.unop) ≫ s.val = s.val
    rw [joinMap_id, Category.id_comp]
  map_comp f g := by
    funext s
    apply Subtype.ext
    change joinMap (g.unop ≫ f.unop) ≫ s.val =
      joinMap g.unop ≫ (joinMap f.unop ≫ s.val)
    rw [joinMap_comp, Category.assoc]

theorem base_leg (q : SimplexCategoryᵒᵖ) (s : (rightMapping X a b).obj q) :
    baseIncl q.unop.len ≫ s.val = (SSet.const a : Δ[0] ⟶ X) := by
  rw [← SSet.yonedaEquiv_symm_zero]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact (point_vertex _ (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).symm.trans
    s.property.1

theorem last_leg (q : SimplexCategoryᵒᵖ) (s : (rightMapping X a b).obj q) :
    omegaMap q.unop.len ≫ s.val = (SSet.const b : Δ[0] ⟶ X) := by
  rw [← SSet.yonedaEquiv_symm_zero]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact (point_vertex _ (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))).symm.trans
    s.property.2

def forward : rightMapping X a b ⟶ simplexSpace X a b where
  app q s := ⟨simplexIncl q.unop.len ≫ s.val, by
    constructor
    · rw [← Category.assoc, face_eq_collapse, Category.assoc, base_leg, SSet.comp_const]
    · exact last_leg X a b q s⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ s.val) (simplexIncl_naturality α.unop))

def coneOfSimplex (q : SimplexCategoryᵒᵖ) (s : (simplexSpace X a b).obj q) :
    cone q.unop.len ⟶ X := desc q.unop.len s.val (SSet.const a)
      (by rw [s.property.1, SSet.comp_const])

theorem simplex_coneOfSimplex (q : SimplexCategoryᵒᵖ) (s : (simplexSpace X a b).obj q) :
    simplexIncl q.unop.len ≫ coneOfSimplex X a b q s = s.val :=
  simplexIncl_desc _ _ _ _

theorem base_coneOfSimplex (q : SimplexCategoryᵒᵖ) (s : (simplexSpace X a b).obj q) :
    baseIncl q.unop.len ≫ coneOfSimplex X a b q s = SSet.const a :=
  baseIncl_desc _ _ _ _

def backward : simplexSpace X a b ⟶ rightMapping X a b where
  app q s := ⟨coneOfSimplex X a b q s, by
    constructor
    · have hv := point_vertex (baseIncl q.unop.len ≫ coneOfSimplex X a b q s)
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
      refine hv.trans ?_
      rw [base_coneOfSimplex, ← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]
    · change SSet.yonedaEquiv (omegaMap q.unop.len ≫ coneOfSimplex X a b q s) = b
      rw [omegaMap, Category.assoc, simplex_coneOfSimplex, s.property.2,
        ← SSet.yonedaEquiv_symm_zero, Equiv.apply_symm_apply]⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    apply pushout.hom_ext
    · change simplexIncl r.unop.len ≫ coneOfSimplex X a b r
          ((simplexSpace X a b).map α s) =
        simplexIncl r.unop.len ≫ coneMap α.unop ≫ coneOfSimplex X a b q s
      rw [simplex_coneOfSimplex, ← Category.assoc, simplexIncl_naturality,
        Category.assoc, simplex_coneOfSimplex]
      rfl
    · change baseIncl r.unop.len ≫ coneOfSimplex X a b r
          ((simplexSpace X a b).map α s) =
        baseIncl r.unop.len ≫ coneMap α.unop ≫ coneOfSimplex X a b q s
      rw [base_coneOfSimplex, ← Category.assoc, baseIncl_naturality, base_coneOfSimplex]

def presentationIso : rightMapping X a b ≅ simplexSpace X a b where
  hom := forward X a b
  inv := backward X a b
  hom_inv_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    apply pushout.hom_ext
    · exact simplex_coneOfSimplex X a b q ((forward X a b).app q s)
    · exact (base_coneOfSimplex X a b q ((forward X a b).app q s)).trans
        (base_leg X a b q s).symm
  inv_hom_id := by
    apply NatTrans.ext
    funext q s
    apply Subtype.ext
    exact simplex_coneOfSimplex X a b q s

end
end DaggerNativeRightConeSimplexPresentation
