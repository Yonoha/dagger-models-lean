import OriginalGadgetsOver
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable (P Q : Code.{u})

/-- Concatenate the actual necklace factors, including either empty list. -/
def tensorFactor : Fin (P.arity + Q.arity) → NecklaceCode :=
  Fin.append P.factor Q.factor

@[simp] theorem tensorFactor_left (i : Fin P.arity) :
    tensorFactor P Q (Fin.castAdd Q.arity i) = P.factor i :=
  Fin.append_left _ _ _

@[simp] theorem tensorFactor_right (i : Fin Q.arity) :
    tensorFactor P Q (Fin.natAdd P.arity i) = Q.factor i :=
  Fin.append_right _ _ _

/-- The first projection of the concatenated finite product. -/
def tensorLeftMap : productSpace (P.arity + Q.arity) (tensorFactor P Q) ⟶ P.space :=
  Pi.lift (fun i ↦
    Pi.π (fun j ↦ (tensorFactor P Q j).toSSet) (Fin.castAdd Q.arity i) ≫
      eqToHom (show (tensorFactor P Q (Fin.castAdd Q.arity i)).toSSet =
        (P.factor i).toSSet from by rw [tensorFactor_left]))

/-- The second projection of the concatenated finite product. -/
def tensorRightMap : productSpace (P.arity + Q.arity) (tensorFactor P Q) ⟶ Q.space :=
  Pi.lift (fun i ↦
    Pi.π (fun j ↦ (tensorFactor P Q j).toSSet) (Fin.natAdd P.arity i) ≫
      eqToHom (show (tensorFactor P Q (Fin.natAdd P.arity i)).toSSet =
        (Q.factor i).toSSet from by rw [tensorFactor_right]))

/-- The literal finite-product realization agrees with the cartesian tensor in `SSet`. -/
def tensorSpaceIso : productSpace (P.arity + Q.arity) (tensorFactor P Q) ≅
    P.space ⊗ Q.space where
  hom := CartesianMonoidalCategory.lift (tensorLeftMap P Q) (tensorRightMap P Q)
  inv := Pi.lift (Fin.addCases
    (fun i ↦ (CartesianMonoidalCategory.fst P.space Q.space ≫
      Pi.π (fun j ↦ (P.factor j).toSSet) i) ≫
        eqToHom (show (P.factor i).toSSet =
          (tensorFactor P Q (Fin.castAdd Q.arity i)).toSSet from by
            rw [tensorFactor_left]))
    (fun i ↦ (CartesianMonoidalCategory.snd P.space Q.space ≫
      Pi.π (fun j ↦ (Q.factor j).toSSet) i) ≫
        eqToHom (show (Q.factor i).toSSet =
          (tensorFactor P Q (Fin.natAdd P.arity i)).toSSet from by
            rw [tensorFactor_right])))
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [tensorLeftMap, tensorFactor, Category.assoc]
    · simp [tensorRightMap, tensorFactor, Category.assoc]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Pi.hom_ext
      intro i
      simp [tensorLeftMap, tensorFactor, Category.assoc]
    · apply Pi.hom_ext
      intro i
      simp [tensorRightMap, tensorFactor, Category.assoc]

theorem tensorSpaceIso_hom_fst :
    (tensorSpaceIso P Q).hom ≫ CartesianMonoidalCategory.fst P.space Q.space =
      tensorLeftMap P Q := CartesianMonoidalCategory.lift_fst _ _

theorem tensorSpaceIso_hom_snd :
    (tensorSpaceIso P Q).hom ≫ CartesianMonoidalCategory.snd P.space Q.space =
      tensorRightMap P Q := CartesianMonoidalCategory.lift_snd _ _

theorem tensorSpaceIso_inv_left :
    (tensorSpaceIso P Q).inv ≫ tensorLeftMap P Q =
      CartesianMonoidalCategory.fst P.space Q.space := by
  rw [← tensorSpaceIso_hom_fst P Q, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

theorem tensorSpaceIso_inv_right :
    (tensorSpaceIso P Q).inv ≫ tensorRightMap P Q =
      CartesianMonoidalCategory.snd P.space Q.space := by
  rw [← tensorSpaceIso_hom_snd P Q, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

private theorem vertexValue_eqToHom {T U : NecklaceCode} (h : T = U)
    (x : T.toSSet.obj (op ⦋0⦌)) :
    ((U.verticesEquiv
      ((eqToHom (congrArg (fun V : NecklaceCode ↦ V.toSSet) h)).app _ x)).down).val =
      ((T.verticesEquiv x).down).val := by
  cases h
  rfl

private theorem tensorVertex_left (x : (P.space ⊗ Q.space).obj (op ⦋0⦌))
    (i : Fin P.arity) :
    (vertex (P.arity + Q.arity) (tensorFactor P Q) (Fin.castAdd Q.arity i)
      ((tensorSpaceIso P Q).inv.app _ x)).val = (vertex P.arity P.factor i x.1).val := by
  let z := (tensorSpaceIso P Q).inv.app (op ⦋0⦌) x
  let t := (Pi.π (fun j ↦ (tensorFactor P Q j).toSSet)
    (Fin.castAdd Q.arity i)).app (op ⦋0⦌) z
  have ht := vertexValue_eqToHom (tensorFactor_left P Q i) t
  have h := congrFun
    (NatTrans.congr_app (tensorSpaceIso_inv_left P Q) (op ⦋0⦌)) x
  have hi := congrArg
    (fun y : P.space.obj (op ⦋0⦌) ↦ (vertex P.arity P.factor i y).val) h
  calc
    _ = ((P.factor i).verticesEquiv
        ((eqToHom (congrArg (fun V : NecklaceCode ↦ V.toSSet)
          (tensorFactor_left P Q i))).app _ t)).down.val := ht.symm
    _ = (vertex P.arity P.factor i ((tensorLeftMap P Q).app _ z)).val := by
      have hπ : tensorLeftMap P Q ≫ Pi.π (fun j ↦ (P.factor j).toSSet) i =
          Pi.π (fun j ↦ (tensorFactor P Q j).toSSet) (Fin.castAdd Q.arity i) ≫
            eqToHom (show (tensorFactor P Q (Fin.castAdd Q.arity i)).toSSet =
              (P.factor i).toSSet from by rw [tensorFactor_left]) := by
        unfold tensorLeftMap
        exact Pi.lift_π _ i
      have heq := congrFun (NatTrans.congr_app hπ (op ⦋0⦌)) z
      exact congrArg
        (fun v : (P.factor i).toSSet.obj (op ⦋0⦌) ↦
          ((P.factor i).verticesEquiv v).down.val) heq.symm
    _ = (vertex P.arity P.factor i x.1).val := hi

private theorem tensorVertex_right (x : (P.space ⊗ Q.space).obj (op ⦋0⦌))
    (i : Fin Q.arity) :
    (vertex (P.arity + Q.arity) (tensorFactor P Q) (Fin.natAdd P.arity i)
      ((tensorSpaceIso P Q).inv.app _ x)).val = (vertex Q.arity Q.factor i x.2).val := by
  let z := (tensorSpaceIso P Q).inv.app (op ⦋0⦌) x
  let t := (Pi.π (fun j ↦ (tensorFactor P Q j).toSSet)
    (Fin.natAdd P.arity i)).app (op ⦋0⦌) z
  have ht := vertexValue_eqToHom (tensorFactor_right P Q i) t
  have h := congrFun
    (NatTrans.congr_app (tensorSpaceIso_inv_right P Q) (op ⦋0⦌)) x
  have hi := congrArg
    (fun y : Q.space.obj (op ⦋0⦌) ↦ (vertex Q.arity Q.factor i y).val) h
  calc
    _ = ((Q.factor i).verticesEquiv
        ((eqToHom (congrArg (fun V : NecklaceCode ↦ V.toSSet)
          (tensorFactor_right P Q i))).app _ t)).down.val := ht.symm
    _ = (vertex Q.arity Q.factor i ((tensorRightMap P Q).app _ z)).val := by
      have hπ : tensorRightMap P Q ≫ Pi.π (fun j ↦ (Q.factor j).toSSet) i =
          Pi.π (fun j ↦ (tensorFactor P Q j).toSSet) (Fin.natAdd P.arity i) ≫
            eqToHom (show (tensorFactor P Q (Fin.natAdd P.arity i)).toSSet =
              (Q.factor i).toSSet from by rw [tensorFactor_right]) := by
        unfold tensorRightMap
        exact Pi.lift_π _ i
      have heq := congrFun (NatTrans.congr_app hπ (op ⦋0⦌)) z
      exact congrArg
        (fun v : (Q.factor i).toSSet.obj (op ⦋0⦌) ↦
          ((Q.factor i).verticesEquiv v).down.val) heq.symm
    _ = (vertex Q.arity Q.factor i x.2).val := hi

/-- Product gadget with the two original chosen endpoints and every factor retained. -/
def Code.tensor : Code.{u} where
  arity := P.arity + Q.arity
  factor := tensorFactor P Q
  alpha := (tensorSpaceIso P Q).inv.app _ ⟨P.alpha, Q.alpha⟩
  omega := (tensorSpaceIso P Q).inv.app _ ⟨P.omega, Q.omega⟩
  comparable := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · change (vertex _ _ (Fin.castAdd Q.arity j) _).val ≤
        (vertex _ _ (Fin.castAdd Q.arity j) _).val
      rw [tensorVertex_left P Q, tensorVertex_left P Q]
      exact P.comparable j
    · change (vertex _ _ (Fin.natAdd P.arity j) _).val ≤
        (vertex _ _ (Fin.natAdd P.arity j) _).val
      rw [tensorVertex_right P Q, tensorVertex_right P Q]
      exact Q.comparable j

/-- A genuine endpoint-preserving projection in the gadget category. -/
def tensorProjectionLeft : Hom (P.tensor Q) P where
  map := tensorLeftMap P Q
  alpha := by
    change ((tensorSpaceIso P Q).inv ≫ tensorLeftMap P Q).app _
      ⟨P.alpha, Q.alpha⟩ = P.alpha
    rw [tensorSpaceIso_inv_left]
    rfl
  omega := by
    change ((tensorSpaceIso P Q).inv ≫ tensorLeftMap P Q).app _
      ⟨P.omega, Q.omega⟩ = P.omega
    rw [tensorSpaceIso_inv_left]
    rfl

/-- The other genuine endpoint-preserving projection. -/
def tensorProjectionRight : Hom (P.tensor Q) Q where
  map := tensorRightMap P Q
  alpha := by
    change ((tensorSpaceIso P Q).inv ≫ tensorRightMap P Q).app _
      ⟨P.alpha, Q.alpha⟩ = Q.alpha
    rw [tensorSpaceIso_inv_right]
    rfl
  omega := by
    change ((tensorSpaceIso P Q).inv ≫ tensorRightMap P Q).app _
      ⟨P.omega, Q.omega⟩ = Q.omega
    rw [tensorSpaceIso_inv_right]
    rfl

/-- Pair two endpoint-preserving maps into the product gadget. -/
def tensorLift {R : Code.{u}} (f : R ⟶ P) (g : R ⟶ Q) : R ⟶ P.tensor Q where
  map := CartesianMonoidalCategory.lift f.map g.map ≫ (tensorSpaceIso P Q).inv
  alpha := by
    change (tensorSpaceIso P Q).inv.app _
      ((CartesianMonoidalCategory.lift f.map g.map).app _ R.alpha) =
        (tensorSpaceIso P Q).inv.app _ ⟨P.alpha, Q.alpha⟩
    apply congrArg (fun x : (P.space ⊗ Q.space).obj (op ⦋0⦌) ↦
      (tensorSpaceIso P Q).inv.app _ x)
    apply Prod.ext
    · change (CartesianMonoidalCategory.lift f.map g.map ≫
        CartesianMonoidalCategory.fst P.space Q.space).app _ R.alpha = P.alpha
      rw [CartesianMonoidalCategory.lift_fst]
      exact f.alpha
    · change (CartesianMonoidalCategory.lift f.map g.map ≫
        CartesianMonoidalCategory.snd P.space Q.space).app _ R.alpha = Q.alpha
      rw [CartesianMonoidalCategory.lift_snd]
      exact g.alpha
  omega := by
    change (tensorSpaceIso P Q).inv.app _
      ((CartesianMonoidalCategory.lift f.map g.map).app _ R.omega) =
        (tensorSpaceIso P Q).inv.app _ ⟨P.omega, Q.omega⟩
    apply congrArg (fun x : (P.space ⊗ Q.space).obj (op ⦋0⦌) ↦
      (tensorSpaceIso P Q).inv.app _ x)
    apply Prod.ext
    · change (CartesianMonoidalCategory.lift f.map g.map ≫
        CartesianMonoidalCategory.fst P.space Q.space).app _ R.omega = P.omega
      rw [CartesianMonoidalCategory.lift_fst]
      exact f.omega
    · change (CartesianMonoidalCategory.lift f.map g.map ≫
        CartesianMonoidalCategory.snd P.space Q.space).app _ R.omega = Q.omega
      rw [CartesianMonoidalCategory.lift_snd]
      exact g.omega

theorem tensorLift_projectionLeft {R : Code.{u}} (f : R ⟶ P) (g : R ⟶ Q) :
    tensorLift P Q f g ≫ tensorProjectionLeft P Q = f := by
  apply Hom.ext
  change (CartesianMonoidalCategory.lift f.map g.map ≫ (tensorSpaceIso P Q).inv) ≫
    tensorLeftMap P Q = f.map
  simp only [Category.assoc, tensorSpaceIso_inv_left,
    CartesianMonoidalCategory.lift_fst]

theorem tensorLift_projectionRight {R : Code.{u}} (f : R ⟶ P) (g : R ⟶ Q) :
    tensorLift P Q f g ≫ tensorProjectionRight P Q = g := by
  apply Hom.ext
  change (CartesianMonoidalCategory.lift f.map g.map ≫ (tensorSpaceIso P Q).inv) ≫
    tensorRightMap P Q = g.map
  simp only [Category.assoc, tensorSpaceIso_inv_right,
    CartesianMonoidalCategory.lift_snd]

/-- The two projections jointly determine every gadget arrow into a tensor. -/
theorem tensorHom_ext {R : Code.{u}} {f g : R ⟶ P.tensor Q}
    (hl : f ≫ tensorProjectionLeft P Q = g ≫ tensorProjectionLeft P Q)
    (hr : f ≫ tensorProjectionRight P Q = g ≫ tensorProjectionRight P Q) : f = g := by
  apply Hom.ext
  have hleft := congrArg (fun z : R ⟶ P ↦ z.map) hl
  have hright := congrArg (fun z : R ⟶ Q ↦ z.map) hr
  change f.map ≫ tensorLeftMap P Q = g.map ≫ tensorLeftMap P Q at hleft
  change f.map ≫ tensorRightMap P Q = g.map ≫ tensorRightMap P Q at hright
  have hpair : f.map ≫ (tensorSpaceIso P Q).hom =
      g.map ≫ (tensorSpaceIso P Q).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, tensorSpaceIso_hom_fst] using hleft
    · simpa only [Category.assoc, tensorSpaceIso_hom_snd] using hright
  have h := congrArg (fun k ↦ k ≫ (tensorSpaceIso P Q).inv) hpair
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- The actual gadget diagonal, also valid when its two endpoints coincide. -/
def tensorDiagonal : P ⟶ P.tensor P := tensorLift P P (𝟙 P) (𝟙 P)

theorem tensorDiagonal_projectionLeft :
    tensorDiagonal P ≫ tensorProjectionLeft P P = 𝟙 P :=
  tensorLift_projectionLeft P P (𝟙 P) (𝟙 P)

theorem tensorDiagonal_projectionRight :
    tensorDiagonal P ≫ tensorProjectionRight P P = 𝟙 P :=
  tensorLift_projectionRight P P (𝟙 P) (𝟙 P)

private theorem tensorIso_inv_hom_vertex (x : (P.space ⊗ Q.space).obj (op ⦋0⦌)) :
    (tensorSpaceIso P Q).hom.app _ ((tensorSpaceIso P Q).inv.app _ x) = x := by
  have h := congrFun (NatTrans.congr_app (tensorSpaceIso P Q).inv_hom_id (op ⦋0⦌)) x
  exact h

/-- Pair arbitrary endpoint-preserving gadget arrows, including non-necklace maps. -/
def tensorMap {P' Q' : Code.{u}} (f : Hom P P') (g : Hom Q Q') :
    Hom (P.tensor Q) (P'.tensor Q') where
  map := (tensorSpaceIso P Q).hom ≫ (f.map ⊗ₘ g.map) ≫
    (tensorSpaceIso P' Q').inv
  alpha := by
    change (tensorSpaceIso P' Q').inv.app _
      ((f.map ⊗ₘ g.map).app _
        ((tensorSpaceIso P Q).hom.app _
          ((tensorSpaceIso P Q).inv.app _ ⟨P.alpha, Q.alpha⟩))) =
        (tensorSpaceIso P' Q').inv.app _ ⟨P'.alpha, Q'.alpha⟩
    rw [tensorIso_inv_hom_vertex P Q]
    simp only [SSet.tensorHom_app_apply, f.alpha, g.alpha]
  omega := by
    change (tensorSpaceIso P' Q').inv.app _
      ((f.map ⊗ₘ g.map).app _
        ((tensorSpaceIso P Q).hom.app _
          ((tensorSpaceIso P Q).inv.app _ ⟨P.omega, Q.omega⟩))) =
        (tensorSpaceIso P' Q').inv.app _ ⟨P'.omega, Q'.omega⟩
    rw [tensorIso_inv_hom_vertex P Q]
    simp only [SSet.tensorHom_app_apply, f.omega, g.omega]

theorem tensorMap_projectionLeft {P' Q' : Code.{u}}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorMap P Q f g ≫ tensorProjectionLeft P' Q' =
      tensorProjectionLeft P Q ≫ f := by
  apply Hom.ext
  change ((tensorSpaceIso P Q).hom ≫ (f.map ⊗ₘ g.map) ≫
    (tensorSpaceIso P' Q').inv) ≫ tensorLeftMap P' Q' =
      tensorLeftMap P Q ≫ f.map
  rw [← tensorSpaceIso_hom_fst P Q]
  simp only [Category.assoc, tensorSpaceIso_inv_left,
    CartesianMonoidalCategory.tensorHom_fst]

theorem tensorMap_projectionRight {P' Q' : Code.{u}}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    tensorMap P Q f g ≫ tensorProjectionRight P' Q' =
      tensorProjectionRight P Q ≫ g := by
  apply Hom.ext
  change ((tensorSpaceIso P Q).hom ≫ (f.map ⊗ₘ g.map) ≫
    (tensorSpaceIso P' Q').inv) ≫ tensorRightMap P' Q' =
      tensorRightMap P Q ≫ g.map
  rw [← tensorSpaceIso_hom_snd P Q]
  simp only [Category.assoc, tensorSpaceIso_inv_right,
    CartesianMonoidalCategory.tensorHom_snd]

theorem tensorMap_id : tensorMap P Q (𝟙 P) (𝟙 Q) = 𝟙 (P.tensor Q) := by
  apply Hom.ext
  change (tensorSpaceIso P Q).hom ≫ (𝟙 P.space ⊗ₘ 𝟙 Q.space) ≫
    (tensorSpaceIso P Q).inv = 𝟙 _
  simp

theorem tensorMap_comp {P' P'' Q' Q'' : Code.{u}}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    tensorMap P Q (f ≫ f') (g ≫ g') =
      Hom.comp (tensorMap P Q f g) (tensorMap P' Q' f' g') := by
  apply Hom.ext
  change (tensorSpaceIso P Q).hom ≫ ((f.map ≫ f'.map) ⊗ₘ (g.map ≫ g'.map)) ≫
    (tensorSpaceIso P'' Q'').inv =
      ((tensorSpaceIso P Q).hom ≫ (f.map ⊗ₘ g.map) ≫
        (tensorSpaceIso P' Q').inv) ≫
      ((tensorSpaceIso P' Q').hom ≫ (f'.map ⊗ₘ g'.map) ≫
        (tensorSpaceIso P'' Q'').inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← tensorHom_comp_tensorHom, Category.assoc]

/-- Cartesian product of gadget arrows on the actual gadget category. -/
def gadgetTensor : Code.{u} × Code.{u} ⥤ Code.{u} where
  obj R := R.1.tensor R.2
  map f := tensorMap _ _ f.1 f.2
  map_id R := tensorMap_id R.1 R.2
  map_comp f g := tensorMap_comp _ _ f.1 g.1 f.2 g.2

variable {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
  {c d : Y.obj (op ⦋0⦌)}

/-- Tensor the two actual structure maps to form a gadget over the literal target tensor. -/
def gadgetTensorOverObj (R : GadgetsOver X a b × GadgetsOver Y c d) :
    GadgetsOver (X ⊗ Y) (a, c) (b, d) :=
  ⟨CostructuredArrow.mk (Y := R.1.obj.left.tensor R.2.obj.left)
    ((tensorSpaceIso R.1.obj.left R.2.obj.left).hom ≫
      (R.1.obj.hom ⊗ₘ R.2.obj.hom)), by
    constructor
    · change (R.1.obj.hom ⊗ₘ R.2.obj.hom).app _
        ((tensorSpaceIso R.1.obj.left R.2.obj.left).hom.app _
          ((tensorSpaceIso R.1.obj.left R.2.obj.left).inv.app _
            ⟨R.1.obj.left.alpha, R.2.obj.left.alpha⟩)) = (a, c)
      rw [tensorIso_inv_hom_vertex]
      simp only [SSet.tensorHom_app_apply, R.1.property.1, R.2.property.1]
    · change (R.1.obj.hom ⊗ₘ R.2.obj.hom).app _
        ((tensorSpaceIso R.1.obj.left R.2.obj.left).hom.app _
          ((tensorSpaceIso R.1.obj.left R.2.obj.left).inv.app _
            ⟨R.1.obj.left.omega, R.2.obj.left.omega⟩)) = (b, d)
      rw [tensorIso_inv_hom_vertex]
      simp only [SSet.tensorHom_app_apply, R.1.property.2, R.2.property.2]⟩

/-- The required functor on all over-gadget morphisms. -/
def theta : GadgetsOver X a b × GadgetsOver Y c d ⥤
    GadgetsOver (X ⊗ Y) (a, c) (b, d) where
  obj := gadgetTensorOverObj
  map {R S} h := ObjectProperty.homMk (CostructuredArrow.homMk
    (tensorMap R.1.obj.left R.2.obj.left h.1.hom.left h.2.hom.left) (by
      change ((tensorSpaceIso R.1.obj.left R.2.obj.left).hom ≫
        (h.1.hom.left.map ⊗ₘ h.2.hom.left.map) ≫
        (tensorSpaceIso S.1.obj.left S.2.obj.left).inv) ≫
        ((tensorSpaceIso S.1.obj.left S.2.obj.left).hom ≫
          (S.1.obj.hom ⊗ₘ S.2.obj.hom)) =
          (tensorSpaceIso R.1.obj.left R.2.obj.left).hom ≫
            (R.1.obj.hom ⊗ₘ R.2.obj.hom)
      have h1 : h.1.hom.left.map ≫ S.1.obj.hom = R.1.obj.hom := h.1.hom.w
      have h2 : h.2.hom.left.map ≫ S.2.obj.hom = R.2.obj.hom := h.2.hom.w
      simp only [Category.assoc, Iso.inv_hom_id_assoc,
        tensorHom_comp_tensorHom, h1, h2]))
  map_id R := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact tensorMap_id R.1.obj.left R.2.obj.left
  map_comp h k := by
    apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    exact tensorMap_comp _ _ h.1.hom.left k.1.hom.left h.2.hom.left k.2.hom.left

end

end DaggerOriginalProductGadget
