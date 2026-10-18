import ActualInnerIteratedGadgetProperties
import ActualNecklaceConeGadgetComparison

/-! Reuse the original necklace cofinality proof for EVERY iterate of the SAME native G. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy
open DaggerOriginalProductGadget hiding Code
open DaggerOriginalFlagFlankification DaggerSSetGluing
open DaggerActualInnerIteratedGadgetData
open scoped Simplicial SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerIteratedGadgetNecklaceComparison
noncomputable section

def inclusion (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    NecklacesOver X a b ⥤ Over X a b where
  obj P := ⟨⟨.inl P.code, 0⟩, P.map, P.first, P.last⟩
  map h := ⟨⟨h.hom.map, h.hom.first, h.hom.last⟩, h.w⟩

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : Over X a b)

abbrev Comma := CostructuredArrow (inclusion X a b) Q

def commaToNecklaces : Comma Q ⥤ NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code)
    where
  obj P := ⟨P.left.code, P.hom.hom.map, P.hom.hom.first, P.hom.hom.last⟩
  map {P R} h := ⟨h.left.hom, by
    exact congrArg (fun f : (inclusion X a b).obj P.left ⟶ Q ↦ f.hom.map)
      (CostructuredArrow.w h)⟩

def necklaceOverObj (P : NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code)) :
    NecklacesOver X a b where
  code := P.code
  map := P.map ≫ Q.map
  first := by change Q.map.app _ (P.map.app _ P.code.first) = a; rw [P.first, Q.first]
  last := by change Q.map.app _ (P.map.app _ P.code.last) = b; rw [P.last, Q.last]

def necklacesToComma : NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code) ⥤ Comma Q
    where
  obj P := CostructuredArrow.mk
    (⟨⟨P.map, P.first, P.last⟩, rfl⟩ : (inclusion X a b).obj (necklaceOverObj Q P) ⟶ Q)
  map {P R} h := CostructuredArrow.homMk
    (⟨h.hom, by
      change h.hom.map ≫ (R.map ≫ Q.map) = _
      rw [← Category.assoc, h.w]
      rfl⟩ :
      necklaceOverObj Q P ⟶ necklaceOverObj Q R)
    (by
      apply Over.Hom.ext
      apply DaggerActualInnerIteratedGadgetData.Hom.ext
      exact h.w)
  map_id P := by apply CostructuredArrow.hom_ext; apply NecklacesOver.Hom.ext; rfl
  map_comp h k := by apply CostructuredArrow.hom_ext; apply NecklacesOver.Hom.ext; rfl

theorem comma_original_map (P : Comma Q) :
    ((commaToNecklaces Q).obj P).map ≫ Q.map = P.left.map := P.hom.w

def necklaceRoundtrip : necklacesToComma Q ⋙ commaToNecklaces Q ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ Iso.refl P) (by
    intro P R h
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.hom.map ≫ 𝟙 _ = 𝟙 _ ≫ h.hom.map
    simp)

def commaLeftRoundtripIso (P : Comma Q) :
    ((necklacesToComma Q).obj ((commaToNecklaces Q).obj P)).left ≅ P.left where
  hom := ⟨𝟙 P.left.code, by
    change 𝟙 _ ≫ P.left.map = P.hom.hom.map ≫ Q.map
    rw [Category.id_comp]
    exact P.hom.w.symm⟩
  inv := ⟨𝟙 P.left.code, by
    change 𝟙 _ ≫ (P.hom.hom.map ≫ Q.map) = P.left.map
    rw [Category.id_comp]
    exact P.hom.w⟩
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 P.left.code.toSSet ≫ 𝟙 _ = 𝟙 _
    simp
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change 𝟙 P.left.code.toSSet ≫ 𝟙 _ = 𝟙 _
    simp

def commaRoundtrip : commaToNecklaces Q ⋙ necklacesToComma Q ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ CostructuredArrow.isoMk (commaLeftRoundtripIso Q P) (by
    apply Over.Hom.ext
    apply DaggerActualInnerIteratedGadgetData.Hom.ext
    change 𝟙 _ ≫ P.hom.hom.map = P.hom.hom.map
    exact Category.id_comp _)) (by
    intro P R h
    apply CostructuredArrow.hom_ext
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.left.hom.map ≫ 𝟙 _ = 𝟙 _ ≫ h.left.hom.map
    simp)

/-- The whole actual comma category retains the original gadget map and both endpoints. -/
def commaEquivalence : Comma Q ≌ NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code) :=
  CategoryTheory.Equivalence.mk (commaToNecklaces Q) (necklacesToComma Q)
    (commaRoundtrip Q).symm (necklaceRoundtrip Q)


/-- The original point-map and native monoidal-terminal-map predicates agree. -/
theorem point_GW_of_toUnit {X : SSet.{u}} (h : GW (toUnit X)) : GW (pointMap X) := by
  let e := pointIsTerminal.{u}.uniqueUpToIso
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u}))
  have : WeakEquivalence (toUnit X) := (weakEquivalence_iff_GW _).mpr h
  have he : toUnit X ≫ e.inv = pointMap X := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- Every iterated gadget has a contractible original necklace-index nerve
at its actual endpoints. -/
theorem code_necklace_point_GW (P : Code) :
    GW (pointMap (nerve (NecklacesOver (space.{u} P) (alpha P) (omega P)))) := by
  apply DaggerActualNecklaceConeGadgetComparison.necklace_point_GW_of_original_hom
  exact point_GW_of_toUnit (DaggerActualInnerIteratedGadgetProperties.endpoint_hom_GW P)

theorem commaToNecklaces_GW {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : Over X a b) :
    GW (nerveMap (commaToNecklaces Q)) :=
  nerveMap_geometricW (commaToNecklaces Q) (necklacesToComma Q)
    (Relation.EqvGen.rel _ _ ⟨(commaRoundtrip Q).hom⟩)
    (Relation.EqvGen.rel _ _ ⟨(necklaceRoundtrip Q).hom⟩)

/-- Every actual costructured-arrow category is contractible; the full maps are retained. -/
theorem comma_point_GW {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : Over X a b) :
    GW (pointMap (nerve (Comma Q))) := by
  have : WeakEquivalence (nerveMap (commaToNecklaces Q)) :=
    (weakEquivalence_iff_GW _).mpr (commaToNecklaces_GW Q)
  have : WeakEquivalence
      (pointMap (nerve (NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code)))) :=
    (weakEquivalence_iff_GW _).mpr (code_necklace_point_GW Q.code)
  have he : nerveMap (commaToNecklaces Q) ≫
      pointMap (nerve (NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code))) =
      pointMap (nerve (Comma Q)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The original necklace inclusion is weak after adding all selected fibrant-gadget iterates. -/
theorem inclusion_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (nerveMap (inclusion X a b)) :=
  DaggerNerveTheoremA.nerveMap_GW (inclusion X a b) comma_point_GW

end
end DaggerActualInnerIteratedGadgetNecklaceComparison
