import OriginalProductBeadConstantNat
import NerveHomotopy

set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open scoped SSet.modelCategoryQuillen
open DaggerChosenRigidificationNecklace DaggerNerveHomotopy

universe u

namespace DaggerOriginalProductGadget

noncomputable section

def beadCollapse (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌)) :
    NecklacesOver (beadSpace m dim) a b ⥤ Discrete PUnit :=
  (Functor.const _).obj (Discrete.mk PUnit.unit)

def beadCenter (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    Discrete PUnit ⥤ NecklacesOver (beadSpace m dim) a b :=
  (Functor.const _).obj (edgeOver m dim a b hab)

def beadCollapseToCompletion (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    beadCollapse m dim a b ⋙ beadCenter m dim a b hab ⟶
      completionFunctor m dim a b :=
  constantToCompletionNat m dim a b hab

def beadCenterToId (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    beadCenter m dim a b hab ⋙ beadCollapse m dim a b ⟶
      𝟭 (Discrete PUnit) where
  app _ := 𝟙 _
  naturality _ _ _ := Subsingleton.elim _ _

theorem beadCollapse_geometricW (m : ℕ) (dim : Fin m → ℕ)
    (a b : (beadSpace.{u} m dim).obj (op ⦋0⦌))
    (hab : ∀ i : Fin m, beadCoord m dim i a ≤ beadCoord m dim i b) :
    SSet.KanComplex.W (TopCat.toSSet.map
      (SSet.toTop.map (nerveMap (beadCollapse m dim a b)))) := by
  apply nerveMap_geometricW (beadCollapse m dim a b) (beadCenter m dim a b hab)
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ ⟨beadCollapseToCompletion m dim a b hab⟩)
      (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ ⟨toCompletionNat m dim a b⟩))
  · exact Relation.EqvGen.rel _ _ ⟨beadCenterToId m dim a b hab⟩

end

end DaggerOriginalProductGadget
