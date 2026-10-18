import ChosenNecklaceEnrichment

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable {T : NecklaceCode} {a b : Vertices.{u} T}
variable (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
variable (ha : a ≤ ULift.up j) (hb : ULift.up j ≤ b)

def splitLeft (P : JointPath a b) : JointPath a (ULift.up j) where
  I := P.I ∩ Set.Iic (ULift.up j : Vertices.{u} T)
  left := ⟨P.left, ha⟩
  right := ⟨P.joints j hj ha hb, by
    show (ULift.up j : Vertices.{u} T) ≤ ULift.up j
    exact le_rfl⟩
  left_le v h := P.left_le v h.1
  le_right _ h := h.2
  joints k hk hl hr := ⟨P.joints k hk hl (hr.trans hb), hr⟩

def splitRight (P : JointPath a b) : JointPath (ULift.up j) b where
  I := P.I ∩ Set.Ici (ULift.up j : Vertices.{u} T)
  left := ⟨P.joints j hj ha hb, by
    show (ULift.up j : Vertices.{u} T) ≤ ULift.up j
    exact le_rfl⟩
  right := ⟨P.right, hb⟩
  left_le _ h := h.2
  le_right v h := P.le_right v h.1
  joints k hk hl hr := ⟨P.joints k hk (ha.trans hl) hr, hl⟩

theorem split_union (P : JointPath a b) :
    (splitLeft j hj ha hb P).I ∪ (splitRight j hj ha hb P).I = P.I := by
  ext v
  constructor
  · exact fun h ↦ h.elim (fun h ↦ h.1) (fun h ↦ h.1)
  · intro h
    rcases le_total v (ULift.up j) with hl | hr
    · exact Or.inl ⟨h, hl⟩
    · exact Or.inr ⟨h, hr⟩

theorem splitLeft_union (P : JointPath a (ULift.up j))
    (Q : JointPath (ULift.up j) b) :
    ((P.I ∪ Q.I) ∩ Set.Iic (ULift.up j : Vertices.{u} T)) = P.I := by
  ext v
  constructor
  · intro h
    rcases h.1 with hp | hq
    · exact hp
    · have he : v = ULift.up j := le_antisymm h.2 (Q.left_le v hq)
      exact he.symm ▸ P.right
  · exact fun h ↦ ⟨Or.inl h, P.le_right v h⟩

theorem splitRight_union (P : JointPath a (ULift.up j))
    (Q : JointPath (ULift.up j) b) :
    ((P.I ∪ Q.I) ∩ Set.Ici (ULift.up j : Vertices.{u} T)) = Q.I := by
  ext v
  constructor
  · intro h
    rcases h.1 with hp | hq
    · have he : v = ULift.up j := le_antisymm (P.le_right v hp) h.2
      exact he.symm ▸ Q.left
    · exact hq
  · exact fun h ↦ ⟨Or.inr h, Q.left_le v h⟩

def splitPathEquiv : JointPath a b ≃
    JointPath a (ULift.up j) × JointPath (ULift.up j) b where
  toFun P := (splitLeft j hj ha hb P, splitRight j hj ha hb P)
  invFun x :=
    { I := x.1.I ∪ x.2.I
      left := Or.inl x.1.left
      right := Or.inr x.2.right
      left_le v h := h.elim (x.1.left_le v) (fun h ↦ ha.trans (x.2.left_le v h))
      le_right v h := h.elim (fun h ↦ (x.1.le_right v h).trans hb) (x.2.le_right v)
      joints k hk hl hr := by
        rcases le_total (ULift.up k : Vertices.{u} T) (ULift.up j) with hkj | hjk
        · exact Or.inl (x.1.joints k hk hl hkj)
        · exact Or.inr (x.2.joints k hk hjk hr) }
  left_inv P := JointPath.ext (split_union j hj ha hb P)
  right_inv x := Prod.ext (JointPath.ext (splitLeft_union j x.1 x.2))
    (JointPath.ext (splitRight_union j x.1 x.2))

def splitPathFunctor : JointPath a b ⥤
    JointPath a (ULift.up j) × JointPath (ULift.up j) b where
  obj := splitPathEquiv j hj ha hb
  map h :=
    (⟨⟨⟨fun v hv ↦ ⟨h.1.1.1 hv.1, hv.2⟩⟩⟩⟩,
      ⟨⟨⟨fun v hv ↦ ⟨h.1.1.1 hv.1, hv.2⟩⟩⟩⟩)

def jointSplitIso : nerve (JointPath a b) ≅
    nerve (JointPath a (ULift.up j)) ⊗ nerve (JointPath (ULift.up j) b) where
  hom :=
    { app _ F := ((F ⋙ splitPathFunctor j hj ha hb) ⋙ CategoryTheory.Prod.fst _ _,
        (F ⋙ splitPathFunctor j hj ha hb) ⋙ CategoryTheory.Prod.snd _ _)
      naturality _ _ _ := by funext F; rfl }
  inv := pathComp (⟨a⟩ : NecklaceThickening T) ⟨ULift.up j⟩ ⟨b⟩
  hom_inv_id := by
    ext q F
    exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext
      (split_union j hj ha hb (F.obj i)))
  inv_hom_id := by
    apply NatTrans.ext
    funext q F
    exact Prod.ext
      (CategoryTheory.Functor.ext (fun i ↦ JointPath.ext
        (splitLeft_union j (F.1.obj i) (F.2.obj i))))
      (CategoryTheory.Functor.ext (fun i ↦ JointPath.ext
        (splitRight_union j (F.1.obj i) (F.2.obj i))))

theorem jointSplitIso_inv : (jointSplitIso j hj ha hb).inv =
    pathComp (⟨a⟩ : NecklaceThickening T) ⟨ULift.up j⟩ ⟨b⟩ := rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
