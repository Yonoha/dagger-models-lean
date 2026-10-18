import ActualNecklaceConeGadgets
import ActualCounitRightConeHomContractibility
import OriginalFlagP2CompleteReconciledRecovered
import OriginalQuillenAHomotopyReconciledRecovered
import ChosenFlagOriginalHomIso

/-! The necklace inclusion into the common necklace/cone category is geometrically weak.
The proof uses the original P2 span and nerve Theorem A. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy
open DaggerOriginalProductGadget hiding Code
open DaggerOriginalFlagFlankification DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualNecklaceConeGadgetComparison
noncomputable section
open DaggerActualNecklaceConeGadgets

def terminalNecklace (T : NecklaceCode) : NecklacesOver T.toSSet T.first T.last :=
  ⟨T, 𝟙 _, rfl, rfl⟩

def necklaceCollapse (T : NecklaceCode) :
    NecklacesOver T.toSSet T.first T.last ⥤ Discrete PUnit.{u + 1} :=
  (Functor.const _).obj (Discrete.mk PUnit.unit)

def necklaceCenter (T : NecklaceCode) :
    Discrete PUnit.{u + 1} ⥤ NecklacesOver T.toSSet T.first T.last :=
  (Functor.const _).obj (terminalNecklace T)

def necklaceToCenter (T : NecklaceCode) :
    𝟭 _ ⟶ necklaceCollapse T ⋙ necklaceCenter T where
  app P := ⟨⟨P.map, P.first, P.last⟩, Category.comp_id _⟩
  naturality P R h := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    change h.hom.map ≫ R.map = P.map ≫ 𝟙 _
    rw [Category.comp_id]
    exact h.w

def necklaceCenterToId (T : NecklaceCode) :
    necklaceCenter T ⋙ necklaceCollapse T ⟶ 𝟭 (Discrete PUnit.{u + 1}) where
  app _ := eqToHom (Subsingleton.elim _ _)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The identity necklace is terminal in the full category of necklaces over itself. -/
theorem necklace_point_GW (T : NecklaceCode) :
    GW (pointMap (nerve (NecklacesOver T.toSSet T.first T.last))) := by
  have : WeakEquivalence (nerveMap (necklaceCollapse T)) :=
    (weakEquivalence_iff_GW _).2
      (nerveMap_geometricW (necklaceCollapse T) (necklaceCenter T)
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨necklaceToCenter T⟩))
        (Relation.EqvGen.rel _ _ ⟨necklaceCenterToId T⟩))
  have he : nerveMap (necklaceCollapse T) ≫ (nerveDiscreteIso PUnit).hom =
      pointMap (nerve (NecklacesOver T.toSSet T.first T.last)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← he]
  infer_instance

/-- P2 transports contraction of the unchanged original Hom to its necklace-index nerve. -/
theorem necklace_point_GW_of_original_hom (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (h : GW (pointMap (RV X a ⟶[SSet.{u}] RV X b))) :
    GW (pointMap (nerve (NecklacesOver X a b))) := by
  have : WeakEquivalence (pointMap (RV X a ⟶[SSet.{u}] RV X b)) :=
    (weakEquivalence_iff_GW _).2 h
  have he : (flagOriginalHomIso X a b).hom ≫
      pointMap (RV X a ⟶[SSet.{u}] RV X b) = pointMap (flagHom X a b) :=
    pointIsTerminal.hom_ext _ _
  have : WeakEquivalence (pointMap (flagHom X a b)) := by rw [← he]; infer_instance
  have : WeakEquivalence (originalEpsilon X a b) :=
    (weakEquivalence_iff_GW _).2 (originalP2_both_GW X a b).1
  have : WeakEquivalence (originalPi X a b) :=
    (weakEquivalence_iff_GW _).2 (originalP2_both_GW X a b).2
  have hc : originalPi X a b ≫ pointMap (nerve (NecklacesOver X a b)) =
      originalEpsilon X a b ≫ pointMap (flagHom X a b) := pointIsTerminal.hom_ext _ _
  have hw : WeakEquivalence (originalPi X a b ≫ pointMap (nerve (NecklacesOver X a b))) := by
    rw [hc]
    infer_instance
  exact (weakEquivalence_iff_GW _).1 ((weakEquivalence_precomp_iff _ _).1 hw)

/-- Both kinds of original gadget have a contractible necklace-index nerve. -/
theorem code_necklace_point_GW (P : Code) :
    GW (pointMap (nerve (NecklacesOver (space.{u} P) (alpha P) (omega P)))) := by
  cases P with
  | inl T => exact necklace_point_GW T
  | inr n =>
    apply necklace_point_GW_of_original_hom
    exact DaggerActualCounitRightConeHomContractibility.Q_point_GW n

theorem commaToNecklaces_GW {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : Over X a b) :
    GW (nerveMap (commaToNecklaces Q)) :=
  nerveMap_geometricW (commaToNecklaces Q) (necklacesToComma Q)
    (Relation.EqvGen.rel _ _ ⟨(commaRoundtrip Q).hom⟩)
    (Relation.EqvGen.rel _ _ ⟨(necklaceRoundtrip Q).hom⟩)

/-- Every actual costructured-arrow category of the inclusion is weakly contractible. -/
theorem comma_point_GW {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} (Q : Over X a b) :
    GW (pointMap (nerve (Comma Q))) := by
  have : WeakEquivalence (nerveMap (commaToNecklaces Q)) :=
    (weakEquivalence_iff_GW _).2 (commaToNecklaces_GW Q)
  have : WeakEquivalence
      (pointMap (nerve (NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code)))) :=
    (weakEquivalence_iff_GW _).2 (code_necklace_point_GW Q.code)
  have he : nerveMap (commaToNecklaces Q) ≫
      pointMap (nerve (NecklacesOver (space Q.code) (alpha Q.code) (omega Q.code))) =
      pointMap (nerve (Comma Q)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).1
  rw [← he]
  infer_instance

/-- Adding all original right cones does not change the necklace-index nerve up to GW. -/
theorem inclusion_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (nerveMap (inclusion X a b)) :=
  DaggerNerveTheoremA.nerveMap_GW (inclusion X a b) comma_point_GW

end
end DaggerActualNecklaceConeGadgetComparison
