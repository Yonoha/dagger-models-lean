import IntervalCompletionMaps

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerIntervalNecklaceCompletion

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {a b : (E.{u}).obj (op ⦋0⦌)}

def completeObject (P : NecklacesOver (E.{u}) a b) : NecklacesOver (E.{u}) a b where
  code := single P.code.len
  map := (singleIso P.code.len).hom ≫ completeMap P.code P.map
  first := by
    change (completeMap P.code P.map).app _ ((singleIso P.code.len).hom.app _
      ((single P.code.len).verticesEquiv.symm (ULift.up 0))) = a
    rw [singleIso_vertex_symm, completeMap_vertex]
    exact P.first
  last := by
    change (completeMap P.code P.map).app _ ((singleIso P.code.len).hom.app _
      ((single P.code.len).verticesEquiv.symm (ULift.up (Fin.last P.code.len)))) = b
    rw [singleIso_vertex_symm, completeMap_vertex]
    exact P.last

def completionInclusion (P : NecklacesOver (E.{u}) a b) :
    NecklacesOver.Hom P (completeObject P) where
  hom := inclusionToSingle P.code
  w := by
    change (P.code.inclusion ≫ (singleIso P.code.len).inv) ≫
      ((singleIso P.code.len).hom ≫ completeMap P.code P.map) = P.map
    rw [Category.assoc, Iso.inv_hom_id_assoc, inclusion_completeMap]

def completionMap {P Q : NecklacesOver (E.{u}) a b} (g : NecklacesOver.Hom P Q) :
    NecklacesOver.Hom (completeObject P) (completeObject Q) where
  hom := completedHom g.hom
  w := by
    change ((singleIso P.code.len).hom ≫ _ ≫ (singleIso Q.code.len).inv) ≫
      ((singleIso Q.code.len).hom ≫ completeMap Q.code Q.map) =
        (singleIso P.code.len).hom ≫ completeMap P.code P.map
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [completeMap_naturality g.hom.map P.map Q.map g.w]

/-- All endpoint-preserving over-E maps are retained, including all collapsed maps. -/
def completion (a b : (E.{u}).obj (op ⦋0⦌)) :
    NecklacesOver (E.{u}) a b ⥤ NecklacesOver (E.{u}) a b where
  obj := completeObject
  map := completionMap
  map_id P := by
    apply NecklacesOver.Hom.ext
    exact completedHom_id P.code
  map_comp f g := by
    apply NecklacesOver.Hom.ext
    exact completedHom_comp f.hom g.hom

/-- The original union inclusions form a natural transformation over the same E. -/
def completionInclusions (a b : (E.{u}).obj (op ⦋0⦌)) :
    𝟭 (NecklacesOver (E.{u}) a b) ⟶ completion a b where
  app := completionInclusion
  naturality := by
    intro P Q f
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (inclusionToSingle_naturality f.hom).symm

theorem completion_original_inclusion (P : NecklacesOver (E.{u}) a b) :
    (completionInclusion P).hom.map ≫ (singleIso P.code.len).hom = P.code.inclusion := by
  change (P.code.inclusion ≫ (singleIso P.code.len).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem completion_under_first (P : NecklacesOver (E.{u}) a b) :
    (completionInclusion P).hom.map.app _ P.code.first = (completeObject P).code.first :=
  (completionInclusion P).hom.first

theorem completion_under_last (P : NecklacesOver (E.{u}) a b) :
    (completionInclusion P).hom.map.app _ P.code.last = (completeObject P).code.last :=
  (completionInclusion P).hom.last

theorem completion_over (P : NecklacesOver (E.{u}) a b) :
    (completionInclusion P).hom.map ≫ (completeObject P).map = P.map :=
  (completionInclusion P).w

theorem completion_operator {P Q : NecklacesOver (E.{u}) a b} (g : NecklacesOver.Hom P Q)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (x : P.code.toSSet.obj q) :
    Q.code.toSSet.map α (g.hom.map.app q x) =
      g.hom.map.app r (P.code.toSSet.map α x) :=
  (congrFun (g.hom.map.naturality α) x).symm

theorem zero_endpoints (P : NecklacesOver (E.{u}) a b) (h : P.code.len = 0) : a = b := by
  have hl : (0 : Fin (P.code.len + 1)) = Fin.last P.code.len := by
    apply Fin.ext
    exact h.symm
  have he : P.code.first = P.code.last := congrArg
    (fun k ↦ P.code.verticesEquiv.symm (ULift.up k)) hl
  exact P.first.symm.trans ((congrArg (P.map.app _) he).trans P.last)

end

end DaggerIntervalNecklaceCompletion
