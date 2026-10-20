import ChosenNecklaceSliceEnriched
import ChosenNecklacePathEndpoints

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} (q : SimplexCategoryᵒᵖ)

theorem chainDiagonal (a : Vertices.{u} T) (F : ChainHom q a a) : F = chainId q a :=
  CategoryTheory.Functor.ext (fun i ↦ @Subsingleton.elim (JointPath a a)
    JointPath.diagonalSubsingleton (F.obj i) ((chainId q a).obj i))

variable (j : Fin (T.len + 1)) (hj : j ∈ T.joints)

theorem splitChainLeft_at_right {a : Vertices.{u} T} (ha : a ≤ ULift.up j)
    (F : ChainHom q a (ULift.up j)) : splitChainLeft q j hj ha le_rfl F = F := by
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change (F.obj i).I ∩ Set.Iic (ULift.up j) = (F.obj i).I
    ext v
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, (F.obj i).le_right v h⟩⟩))

theorem splitChainRight_at_right {a : Vertices.{u} T} (ha : a ≤ ULift.up j)
    (F : ChainHom q a (ULift.up j)) :
    splitChainRight q j hj ha le_rfl F = chainId q (ULift.up j) := chainDiagonal q _ _

variable {D : DaggerModels.SimplicialCat.{u,u}} {d : Vertices.{u} T → D.Obj}
variable (S : SliceSSetMaps j D d)

theorem glueChain_left {a b : Vertices.{u} T}
    (ha : a ≤ ULift.up j) (hb : b ≤ ULift.up j) (F : ChainHom q a b) :
    glueChain q j hj (S.degree q) F = (S.left a b ha hb).app q F := by
  by_cases hja : ULift.up j ≤ a
  · have ea : a = ULift.up j := le_antisymm ha hja
    subst a
    have eb : b = ULift.up j := le_antisymm hb (chain_le q F)
    subst b
    rw [chainDiagonal q (ULift.up j) F]
    exact (glueChain_id q j hj (S.degree q) _).trans
      ((S.degree q).left_id _ le_rfl).symm
  · by_cases hjb : ULift.up j ≤ b
    · have eb : b = ULift.up j := le_antisymm hb hjb
      subst b
      simp only [glueChain, dif_neg hja, dif_pos le_rfl]
      rw [splitChainLeft_at_right, splitChainRight_at_right,
        (S.degree q).right_id, Category.comp_id]
      rfl
    · simp only [glueChain, dif_neg hja, dif_neg hjb]
      rfl

theorem glueChain_right {a b : Vertices.{u} T}
    (ha : ULift.up j ≤ a) (hb : ULift.up j ≤ b) (F : ChainHom q a b) :
    glueChain q j hj (S.degree q) F = (S.right a b ha hb).app q F := by
  simp only [glueChain, dif_pos ha]
  rfl

namespace SliceSSetMaps

theorem hom_left {a b : Vertices.{u} T} (ha : a ≤ ULift.up j) (hb : b ≤ ULift.up j) :
    S.hom hj a b = S.left a b ha hb := by
  apply NatTrans.ext
  funext q F
  exact glueChain_left q j hj S ha hb F

theorem hom_right {a b : Vertices.{u} T} (ha : ULift.up j ≤ a) (hb : ULift.up j ≤ b) :
    S.hom hj a b = S.right a b ha hb := by
  apply NatTrans.ext
  funext q F
  exact glueChain_right q j hj S ha hb F

end SliceSSetMaps

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
