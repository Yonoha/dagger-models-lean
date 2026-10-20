import IntervalFlagPath
import ChosenFlagEnrichment

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalFlagContraction

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open NecklaceCode
open DaggerIntervalNecklaceCompletion

variable {a b : (E.{u}).obj (op ⦋0⦌)}

def endpointOrder (N : ℕ) : Fin 2 →o Fin (N + 1) where
  toFun i := if i = 0 then 0 else Fin.last N
  monotone' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

def endpointCodeMap (N : ℕ) : Hom.{u} (single 1) (single N) where
  map := (singleIso 1).hom ≫
    SSet.stdSimplex.map (SimplexCategory.Hom.mk (endpointOrder N) : ⦋1⦌ ⟶ ⦋N⦌) ≫
      (singleIso N).inv
  first := by
    change (singleIso N).inv.app _
      ((SSet.stdSimplex.map _).app _ ((singleIso 1).hom.app _
        ((single 1).verticesEquiv.symm (ULift.up 0)))) =
      (single N).verticesEquiv.symm (ULift.up 0)
    rw [singleIso_vertex_symm]
    change (singleIso N).inv.app _ (SSet.stdSimplex.obj₀Equiv.symm 0) = _
    exact singleIso_inv_vertex N 0
  last := by
    change (singleIso N).inv.app _
      ((SSet.stdSimplex.map _).app _ ((singleIso 1).hom.app _
        ((single 1).verticesEquiv.symm (ULift.up (Fin.last 1))))) =
      (single N).verticesEquiv.symm (ULift.up (Fin.last N))
    rw [singleIso_vertex_symm]
    change (singleIso N).inv.app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last N)) = _
    exact singleIso_inv_vertex N (Fin.last N)

theorem endpointCodeMap_vertex (N : ℕ) (i : Fin 2) :
    mapVertices (endpointCodeMap.{u} N).map (ULift.up i) =
      ULift.up (endpointOrder N i) := by
  dsimp [mapVertices, endpointCodeMap]
  rw [singleIso_vertex_symm]
  change (single N).verticesEquiv ((singleIso N).inv.app _
    (SSet.stdSimplex.obj₀Equiv.symm (endpointOrder N i))) = _
  rw [singleIso_inv_vertex, Equiv.apply_symm_apply]

/-- Whole original E-valued map equation, not only endpoint agreement. -/
theorem endpoint_completeMap (P : NecklacesOver (E.{u}) a b) :
    (endpointCodeMap P.code.len).map ≫ (completeObject P).map =
      (edgeObject a b).map := by
  apply DaggerIntervalNecklaceCompletion.hom_ext_vertices
  intro v
  obtain ⟨⟨i⟩, rfl⟩ := (single 1).verticesEquiv.symm.surjective v
  fin_cases i
  · change (completeObject P).map.app _
      ((endpointCodeMap P.code.len).map.app _ (single 1).first) = _
    rw [(endpointCodeMap P.code.len).first]
    change (completeObject P).map.app _ (completeObject P).code.first =
      (edgeObject a b).map.app _ (edgeObject a b).code.first
    exact (completeObject P).first.trans (edgeObject a b).first.symm
  · change (completeObject P).map.app _
      ((endpointCodeMap P.code.len).map.app _ (single 1).last) = _
    rw [(endpointCodeMap P.code.len).last]
    change (completeObject P).map.app _ (completeObject P).code.last =
      (edgeObject a b).map.app _ (edgeObject a b).code.last
    exact (completeObject P).last.trans (edgeObject a b).last.symm

def endpointOverMap (P : NecklacesOver (E.{u}) a b) :
    NecklacesOver.Hom (edgeObject a b) (completeObject P) where
  hom := endpointCodeMap P.code.len
  w := endpoint_completeMap P

theorem endpoint_stdMap (P : NecklacesOver (E.{u}) a b) :
    SSet.stdSimplex.map
      (SimplexCategory.Hom.mk (endpointOrder P.code.len) : ⦋1⦌ ⟶ ⦋P.code.len⦌) ≫
      completeMap P.code P.map = endpointEdge a b := by
  have h := endpoint_completeMap P
  simp only [endpointCodeMap, completeObject, edgeObject, Category.assoc,
    Iso.inv_hom_id_assoc] at h
  exact (cancel_epi (singleIso 1).hom).mp h

theorem endpoint_bottomFlag (N n : ℕ) :
    NecklaceCode.Flag.map (endpointCodeMap.{u} N) (bottomFlag 1 n) = bottomFlag N n := by
  apply NecklaceCode.Flag.ext
  intro i
  change mapVertices (endpointCodeMap N).map ''
    {firstVertex 1, lastVertex 1} = {firstVertex N, lastVertex N}
  rw [Set.image_insert_eq, Set.image_singleton, endpointCodeMap_vertex,
    endpointCodeMap_vertex]
  rfl

def center : (flagHom (E.{u}) a b).obj (op ⦋0⦌) :=
  Quot.mk _ ⟨edgeObject a b, bottomFlag 1 0⟩

def centerAt (q : SimplexCategoryᵒᵖ) : (flagHom (E.{u}) a b).obj q :=
  Quot.mk _ ⟨edgeObject a b, bottomFlag 1 q.unop.len⟩

theorem centerAt_const (q : SimplexCategoryᵒᵖ) (x : (flagHom (E.{u}) a b).obj q) :
    (SSet.const (center (a := a) (b := b))).app q x = centerAt q := rfl

/-- Every completed bottom flag is this one literal supplied-endpoint edge class. -/
theorem completed_bottom_center (P : NecklacesOver (E.{u}) a b)
    (q : SimplexCategoryᵒᵖ) :
    (Quot.mk _ ⟨completeObject P, bottomFlag P.code.len q.unop.len⟩ :
      (flagHom (E.{u}) a b).obj q) = centerAt q :=
  (Quot.sound ⟨endpointOverMap P, (endpoint_bottomFlag _ _).symm⟩).symm

end

end DaggerOriginalIntervalFlagContraction
