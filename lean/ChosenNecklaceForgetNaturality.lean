import ChosenNecklaceForget
import ChosenNecklaceEnrichedCut
import ChosenNecklaceBeadThickening

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

theorem cutNCInclusion_forget (T : NecklaceCode) (j : Fin (T.len + 1)) (right : Bool) :
    cutNCInclusion.{u} T j right ≫ forgetNC T =
      forgetNC (sideCode T j right) ≫ DaggerChosenRigidificationNecklace.T.map
        (SimplexCategory.Hom.mk
          (intervalEmbedding T (sideStart T j right) (sideEnd T j right)
            (sideLe T j right)).toOrderHom : ⦋(sideCode T j right).len⦌ ⟶ ⦋T.len⦌) := by
  have ho : ∀ a, (cutNCInclusion T j right ≫ forgetNC T).obj a =
      (forgetNC (sideCode T j right) ≫ DaggerChosenRigidificationNecklace.T.map
        (SimplexCategory.Hom.mk
          (intervalEmbedding T (sideStart T j right) (sideEnd T j right)
            (sideLe T j right)).toOrderHom : ⦋(sideCode T j right).len⦌ ⟶ ⦋T.len⦌)).obj a :=
    fun _ ↦ rfl
  apply EnrichedFunctor.ext SSet ho
  intro a b
  ext q F
  exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

theorem NCMap_forget {T U : NecklaceCode} (f : NecklaceCode.Hom.{u} T U) :
    NCMap f ≫ forgetNC U = forgetNC T ≫ DaggerChosenRigidificationNecklace.T.map
      (SimplexCategory.Hom.mk (orderMap f.map) : ⦋T.len⦌ ⟶ ⦋U.len⦌) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a b
  ext q F
  exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

theorem beadNC_forget {T : NecklaceCode} (b : T.Bead) :
    beadNC.{u} b ≫ forgetNC T = DaggerChosenRigidificationNecklace.T.map
      (SimplexCategory.Hom.mk b.embedding.toOrderHom : ⦋b.length⦌ ⟶ ⦋T.len⦌) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro a c
  ext q F
  exact CategoryTheory.Functor.ext (fun _ ↦ SimplicialThickening.Path.ext rfl)

theorem singleNCIso_inv_forget (n : ℕ) :
    (singleNCIso.{u} n).inv ≫ forgetNC (single n) = 𝟙 _ := by
  change (singleNCIso n).inv ≫ (singleNCIso n).hom = _
  exact (singleNCIso n).inv_hom_id

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
