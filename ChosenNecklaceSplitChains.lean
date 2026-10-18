import ChosenNecklacePathSplitting

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} (q : SimplexCategoryᵒᵖ)

abbrev ChainHom (a b : Vertices.{u} T) := (pathHom ⟨a⟩ ⟨b⟩).obj q

abbrev chainId (a : Vertices.{u} T) : ChainHom q a a := (pathId ⟨a⟩).app q PUnit.unit

abbrev chainComp {a b c : Vertices.{u} T} (F : ChainHom q a b) (G : ChainHom q b c) :
    ChainHom q a c := (pathComp ⟨a⟩ ⟨b⟩ ⟨c⟩).app q (F, G)

theorem chain_le {a b : Vertices.{u} T} (F : ChainHom q a b) : a ≤ b :=
  (F.obj 0).left_le _ (F.obj 0).right

variable (j : Fin (T.len + 1)) (hj : j ∈ T.joints)

abbrev splitChainLeft {a b : Vertices.{u} T} (ha : a ≤ ULift.up j) (hb : ULift.up j ≤ b)
    (F : ChainHom q a b) : ChainHom q a (ULift.up j) :=
  ((jointSplitIso j hj ha hb).hom.app q F).1

abbrev splitChainRight {a b : Vertices.{u} T} (ha : a ≤ ULift.up j) (hb : ULift.up j ≤ b)
    (F : ChainHom q a b) : ChainHom q (ULift.up j) b :=
  ((jointSplitIso j hj ha hb).hom.app q F).2

theorem chain_split_comp {a b : Vertices.{u} T}
    (ha : a ≤ ULift.up j) (hb : ULift.up j ≤ b) (F : ChainHom q a b) :
    chainComp q (splitChainLeft q j hj ha hb F) (splitChainRight q j hj ha hb F) = F := by
  exact congrFun (NatTrans.congr_app (jointSplitIso j hj ha hb).hom_inv_id q) F

theorem splitChainLeft_comp_right {a b c : Vertices.{u} T}
    (ha : a ≤ ULift.up j) (hb : ULift.up j ≤ b)
    (F : ChainHom q a b) (G : ChainHom q b c) :
    splitChainLeft q j hj ha (hb.trans (chain_le q G)) (chainComp q F G) =
      splitChainLeft q j hj ha hb F := by
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change ((F.obj i).I ∪ (G.obj i).I) ∩ Set.Iic (ULift.up j) =
      (F.obj i).I ∩ Set.Iic (ULift.up j)
    ext v
    constructor
    · rintro ⟨hf | hg, hv⟩
      · exact ⟨hf, hv⟩
      · have he : v = ULift.up j := le_antisymm hv (hb.trans ((G.obj i).left_le v hg))
        subst v
        exact ⟨(F.obj i).joints j hj ha hb, by
          show (ULift.up j : Vertices.{u} T) ≤ ULift.up j
          exact le_rfl⟩
    · rintro ⟨hf, hv⟩
      exact ⟨Or.inl hf, hv⟩))

theorem splitChainRight_comp_right {a b c : Vertices.{u} T}
    (ha : a ≤ ULift.up j) (hb : ULift.up j ≤ b)
    (F : ChainHom q a b) (G : ChainHom q b c) :
    splitChainRight q j hj ha (hb.trans (chain_le q G)) (chainComp q F G) =
      chainComp q (splitChainRight q j hj ha hb F) G := by
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change ((F.obj i).I ∪ (G.obj i).I) ∩ Set.Ici (ULift.up j) =
      ((F.obj i).I ∩ Set.Ici (ULift.up j)) ∪ (G.obj i).I
    ext v
    constructor
    · rintro ⟨hf | hg, hv⟩
      · exact Or.inl ⟨hf, hv⟩
      · exact Or.inr hg
    · rintro (⟨hf, hv⟩ | hg)
      · exact ⟨Or.inl hf, hv⟩
      · exact ⟨Or.inr hg, hb.trans ((G.obj i).left_le v hg)⟩))

theorem splitChainLeft_comp_left {a b c : Vertices.{u} T}
    (hb : b ≤ ULift.up j) (hc : ULift.up j ≤ c)
    (F : ChainHom q a b) (G : ChainHom q b c) :
    splitChainLeft q j hj ((chain_le q F).trans hb) hc (chainComp q F G) =
      chainComp q F (splitChainLeft q j hj hb hc G) := by
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change ((F.obj i).I ∪ (G.obj i).I) ∩ Set.Iic (ULift.up j) =
      (F.obj i).I ∪ ((G.obj i).I ∩ Set.Iic (ULift.up j))
    ext v
    constructor
    · rintro ⟨hf | hg, hv⟩
      · exact Or.inl hf
      · exact Or.inr ⟨hg, hv⟩
    · rintro (hf | ⟨hg, hv⟩)
      · exact ⟨Or.inl hf, ((F.obj i).le_right v hf).trans hb⟩
      · exact ⟨Or.inr hg, hv⟩))

theorem splitChainRight_comp_left {a b c : Vertices.{u} T}
    (hb : b ≤ ULift.up j) (hc : ULift.up j ≤ c)
    (F : ChainHom q a b) (G : ChainHom q b c) :
    splitChainRight q j hj ((chain_le q F).trans hb) hc (chainComp q F G) =
      splitChainRight q j hj hb hc G := by
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change ((F.obj i).I ∪ (G.obj i).I) ∩ Set.Ici (ULift.up j) =
      (G.obj i).I ∩ Set.Ici (ULift.up j)
    ext v
    constructor
    · rintro ⟨hf | hg, hv⟩
      · have he : v = ULift.up j := le_antisymm (((F.obj i).le_right v hf).trans hb) hv
        subst v
        exact ⟨(G.obj i).joints j hj hb hc, by
          show (ULift.up j : Vertices.{u} T) ≤ ULift.up j
          exact le_rfl⟩
      · exact ⟨hg, hv⟩
    · rintro ⟨hg, hv⟩
      exact ⟨Or.inr hg, hv⟩))

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
