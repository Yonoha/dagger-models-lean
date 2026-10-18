import ChosenNecklaceSplitChains

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u v w

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} (q : SimplexCategoryᵒᵖ)
variable (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
variable (D : Type v) [Category.{w} D] (d : Vertices.{u} T → D)

/-- Actual local degree functors with the same object labels on both sides of an original joint. -/
structure SliceChainMaps where
  left : ∀ (a b : Vertices.{u} T), a ≤ ULift.up j → b ≤ ULift.up j →
    ChainHom q a b → (d a ⟶ d b)
  right : ∀ (a b : Vertices.{u} T), ULift.up j ≤ a → ULift.up j ≤ b →
    ChainHom q a b → (d a ⟶ d b)
  left_id : ∀ (a : Vertices.{u} T) (ha : a ≤ ULift.up j),
    left a a ha ha (chainId q a) = 𝟙 (d a)
  right_id : ∀ (a : Vertices.{u} T) (ha : ULift.up j ≤ a),
    right a a ha ha (chainId q a) = 𝟙 (d a)
  left_comp : ∀ (a b c : Vertices.{u} T)
    (ha : a ≤ ULift.up j) (hb : b ≤ ULift.up j) (hc : c ≤ ULift.up j)
    (F : ChainHom q a b) (G : ChainHom q b c),
    left a c ha hc (chainComp q F G) = left a b ha hb F ≫ left b c hb hc G
  right_comp : ∀ (a b c : Vertices.{u} T)
    (ha : ULift.up j ≤ a) (hb : ULift.up j ≤ b) (hc : ULift.up j ≤ c)
    (F : ChainHom q a b) (G : ChainHom q b c),
    right a c ha hc (chainComp q F G) = right a b ha hb F ≫ right b c hb hc G

variable {D d} (S : SliceChainMaps q j D d)

/-- Crossing Homs are the same two original restricted chains, composed in the supplied target. -/
def glueChain {a b : Vertices.{u} T} (F : ChainHom q a b) : d a ⟶ d b :=
  if ha : ULift.up j ≤ a then
    S.right a b ha (ha.trans (chain_le q F)) F
  else if hb : ULift.up j ≤ b then
    S.left a (ULift.up j) (le_of_lt (lt_of_not_ge ha)) le_rfl
        (splitChainLeft q j hj (le_of_lt (lt_of_not_ge ha)) hb F) ≫
      S.right (ULift.up j) b le_rfl hb
        (splitChainRight q j hj (le_of_lt (lt_of_not_ge ha)) hb F)
  else S.left a b (le_of_lt (lt_of_not_ge ha)) (le_of_lt (lt_of_not_ge hb)) F

theorem glueChain_id (a : Vertices.{u} T) :
    glueChain q j hj S (chainId q a) = 𝟙 (d a) := by
  by_cases ha : ULift.up j ≤ a
  · simp only [glueChain, dif_pos ha, S.right_id]
  · simp only [glueChain, dif_neg ha, S.left_id]

theorem glueChain_comp {a b c : Vertices.{u} T}
    (F : ChainHom q a b) (G : ChainHom q b c) :
    glueChain q j hj S (chainComp q F G) =
      glueChain q j hj S F ≫ glueChain q j hj S G := by
  by_cases ha : ULift.up j ≤ a
  · have hb := ha.trans (chain_le q F)
    have hc := hb.trans (chain_le q G)
    simp only [glueChain, dif_pos ha, dif_pos hb, dif_pos hc]
    exact S.right_comp a b c ha hb hc F G
  · by_cases hb : ULift.up j ≤ b
    · have hc := hb.trans (chain_le q G)
      simp only [glueChain, dif_neg ha, dif_pos hb, dif_pos hc]
      rw [splitChainLeft_comp_right, splitChainRight_comp_right, S.right_comp,
        Category.assoc]
    · by_cases hc : ULift.up j ≤ c
      · simp only [glueChain, dif_neg ha, dif_neg hb, dif_pos hc]
        rw [splitChainLeft_comp_left, splitChainRight_comp_left, S.left_comp,
          Category.assoc]
      · simp only [glueChain, dif_neg ha, dif_neg hb, dif_neg hc]
        exact S.left_comp a b c (le_of_lt (lt_of_not_ge ha))
          (le_of_lt (lt_of_not_ge hb)) (le_of_lt (lt_of_not_ge hc)) F G

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
