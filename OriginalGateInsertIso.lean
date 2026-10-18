import OriginalProductSupportBounds

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a v b : X.obj (op ⦋0⦌)) (S : Set (X.obj (op ⦋0⦌)))

/-- Forget the later gates, retaining the actual simplex and the first required gate. -/
def gateInsertHead :
    (flagGateSubcomplex a b (insert v S)).toFunctor ⟶ (flagGateSubcomplex a b {v}).toFunctor :=
  Subfunctor.homOfLe (flagGateSubcomplex_antitone a b
    (Set.singleton_subset_iff.mpr (Set.mem_insert v S)))

variable (hm : ∀ P : NecklacesOver X a b,
  (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- Apply the established one-gate split to the same original simplex. -/
def gateInsertUnderlyingSplit :
    (flagGateSubcomplex a b (insert v S)).toFunctor ⟶ flagHom X a v ⊗ flagHom X v b :=
  gateInsertHead a v b S ≫ (gateHomProductIso a v b hm).hom

variable (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)
  (hS : ∀ w ∈ S, R v w)

/-- The first split retains every later required gate in the right Hom factor. -/
def gateInsertSplit :
    (flagGateSubcomplex a b (insert v S)).toFunctor ⟶
      flagHom X a v ⊗ (flagGateSubcomplex v b S).toFunctor where
  app q x :=
    let p := (gateInsertUnderlyingSplit a v b S hm).app q x
    (p.1, ⟨p.2, by
      have hc : flagCompApp p.1 p.2 = x.val :=
        congrArg Subtype.val (congrFun
          (NatTrans.congr_app (gateHomProductIso a v b hm).hom_inv_id q)
          ((gateInsertHead a v b S).app q x))
      apply (gateTail_support_iff R hanti hbound S hS p.1 p.2).mp
      rw [hc]
      intro w hw
      exact x.property (Set.mem_insert_of_mem v hw)⟩)
  naturality p q α := by
    funext x
    apply Prod.ext
    · have h := congrArg Prod.fst
        (congrFun ((gateInsertUnderlyingSplit a v b S hm).naturality α) x)
      exact h
    · apply Subtype.ext
      have h := congrArg Prod.snd
        (congrFun ((gateInsertUnderlyingSplit a v b S hm).naturality α) x)
      exact h

/-- Original composition retains the first gate and every required gate in the right factor. -/
def gateInsertCompose :
    flagHom X a v ⊗ (flagGateSubcomplex v b S).toFunctor ⟶
      (flagGateSubcomplex a b (insert v S)).toFunctor where
  app q x := ⟨flagCompApp x.1 x.2.val, by
    change insert v S ⊆ flagVertexSupport (flagCompApp x.1 x.2.val)
    rw [flagVertexSupport_comp]
    intro w hw
    rcases Set.mem_insert_iff.mp hw with he | hs
    · exact Or.inl (he.symm ▸ flagVertexSupport_last x.1)
    · exact Or.inr (x.2.property hs)⟩
  naturality p q α := by
    funext x
    apply Subtype.ext
    exact (flagCompApp_operator α x.1 x.2.val).symm

/-- One-gate decomposition restricted to all the remaining gate conditions. -/
def gateInsertIso :
    (flagGateSubcomplex a b (insert v S)).toFunctor ≅
      flagHom X a v ⊗ (flagGateSubcomplex v b S).toFunctor where
  hom := gateInsertSplit a v b S hm R hanti hbound hS
  inv := gateInsertCompose a v b S
  hom_inv_id := by
    apply NatTrans.ext
    funext q x
    apply Subtype.ext
    have h := congrArg Subtype.val (congrFun
      (NatTrans.congr_app (gateHomProductIso a v b hm).hom_inv_id q)
      ((gateInsertHead a v b S).app q x))
    exact h
  inv_hom_id := by
    apply NatTrans.ext
    funext q x
    apply Prod.ext
    · have h := congrArg Prod.fst (congrFun
        (NatTrans.congr_app (gateHomProductIso a v b hm).inv_hom_id q) (x.1, x.2.val))
      exact h
    · apply Subtype.ext
      have h := congrArg Prod.snd (congrFun
        (NatTrans.congr_app (gateHomProductIso a v b hm).inv_hom_id q) (x.1, x.2.val))
      exact h

/-- Inclusion after the inverse is the same original composition, with no new multiplication. -/
theorem gateInsertIso_inv_ι :
    (gateInsertIso a v b S hm R hanti hbound hS).inv ≫
        (flagGateSubcomplex a b (insert v S)).ι =
      (𝟙 (flagHom X a v) ⊗ₘ (flagGateSubcomplex v b S).ι) ≫ flagComposition X a v b := rfl

end

end DaggerOriginalProductGadget
