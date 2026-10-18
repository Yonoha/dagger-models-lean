import ChosenNecklaceCutComparisonObjects
import ChosenNecklaceForgetNaturality

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

/-- Whole original inclusion equation fixes every bead leg and arbitrary necklace-map action. -/
structure CanonicalComparison (T : NecklaceCode) extends LabelledComparison.{u} T where
  inclusion : iso.hom ≫ forgetNC T = C.map T.inclusion ≫ (ρ.app ⦋T.len⦌).hom

def singleCanonicalComparison (n : ℕ) : CanonicalComparison.{u} (single n) where
  toLabelledComparison := singleComparison n
  inclusion := by
    change (singleChosenIso n).hom ≫ forgetNC (single n) = _
    simp only [singleChosenIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Category.assoc, singleNCIso_inv_forget, Category.comp_id, singleIso_hom]
    rfl

variable (T : NecklaceCode) (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
variable (L : CanonicalComparison.{u} (cutLeft T j))
variable (R : CanonicalComparison.{u} (cutRight T j))

theorem cutChosenIso_inclusion :
    (cutChosenIso T j hj L.toLabelledComparison R.toLabelledComparison).hom ≫ forgetNC T =
      C.map T.inclusion ≫ (ρ.app ⦋T.len⦌).hom := by
  apply (chosenCutIsPushout T j hj).hom_ext
  · rw [← Category.assoc, cutChosenIso_left, Category.assoc, cutNCInclusion_forget,
      ← Category.assoc]
    change (L.iso.hom ≫ forgetNC (cutLeft T j)) ≫
      DaggerChosenRigidificationNecklace.T.map
        (SimplexCategory.Hom.mk (intervalEmbedding T 0 j (Fin.zero_le j)).toOrderHom :
          ⦋(cutLeft T j).len⦌ ⟶ ⦋T.len⦌) = _
    rw [L.inclusion]
    let α : ⦋(cutLeft T j).len⦌ ⟶ ⦋T.len⦌ :=
      SimplexCategory.Hom.mk (intervalEmbedding T 0 j (Fin.zero_le j)).toOrderHom
    have hρ := ρ.hom.naturality α
    change C.map (SSet.stdSimplex.map α) ≫ (ρ.app ⦋T.len⦌).hom =
      (ρ.app ⦋(cutLeft T j).len⦌).hom ≫ DaggerChosenRigidificationNecklace.T.map α at hρ
    rw [Category.assoc, ← hρ, ← Category.assoc, ← C.map_comp]
    rw [← intervalι_inclusion T 0 j (Fin.zero_le j), C.map_comp, Category.assoc]
    rfl
  · rw [← Category.assoc, cutChosenIso_right, Category.assoc, cutNCInclusion_forget,
      ← Category.assoc]
    change (R.iso.hom ≫ forgetNC (cutRight T j)) ≫
      DaggerChosenRigidificationNecklace.T.map
        (SimplexCategory.Hom.mk
          (intervalEmbedding T j (Fin.last T.len) (Fin.le_last j)).toOrderHom :
            ⦋(cutRight T j).len⦌ ⟶ ⦋T.len⦌) = _
    rw [R.inclusion]
    let α : ⦋(cutRight T j).len⦌ ⟶ ⦋T.len⦌ :=
      SimplexCategory.Hom.mk
        (intervalEmbedding T j (Fin.last T.len) (Fin.le_last j)).toOrderHom
    have hρ := ρ.hom.naturality α
    change C.map (SSet.stdSimplex.map α) ≫ (ρ.app ⦋T.len⦌).hom =
      (ρ.app ⦋(cutRight T j).len⦌).hom ≫ DaggerChosenRigidificationNecklace.T.map α at hρ
    rw [Category.assoc, ← hρ, ← Category.assoc, ← C.map_comp]
    rw [← intervalι_inclusion T j (Fin.last T.len) (Fin.le_last j),
      C.map_comp, Category.assoc]
    rfl

def cutCanonicalComparison : CanonicalComparison.{u} T where
  toLabelledComparison := cutComparison T j hj L.toLabelledComparison R.toLabelledComparison
  inclusion := cutChosenIso_inclusion T j hj L R

end

end DaggerChosenRigidificationNecklace
