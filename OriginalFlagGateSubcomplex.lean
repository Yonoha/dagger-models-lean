import OriginalFlagVertexSupport

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a b : X.obj (op ⦋0⦌))

/-- The subcomplex of the original flag Hom whose first vertex support contains every given gate. -/
def flagGateSubcomplex (S : Set (X.obj (op ⦋0⦌))) : (flagHom X a b).Subcomplex where
  obj q := {x | S ⊆ flagVertexSupport x}
  map α := by
    intro x hx
    exact hx.trans (flagVertexSupport_operator α x)

theorem flagGateSubcomplex_antitone {S R : Set (X.obj (op ⦋0⦌))} (h : S ⊆ R) :
    flagGateSubcomplex a b R ≤ flagGateSubcomplex a b S := by
  intro q x hx
  exact h.trans hx

theorem flagGateSubcomplex_empty : flagGateSubcomplex a b ∅ = ⊤ := by
  ext q x
  exact ⟨fun _ ↦ trivial, fun _ ↦ Set.empty_subset _⟩

/-- Requiring both gate sets is exactly the intersection inside the original Hom. -/
theorem flagGateSubcomplex_union (S R : Set (X.obj (op ⦋0⦌))) :
    flagGateSubcomplex a b (S ∪ R) = flagGateSubcomplex a b S ⊓ flagGateSubcomplex a b R := by
  ext q x
  exact Set.union_subset_iff

variable {a b} {q r : SimplexCategoryᵒᵖ}

/-- The full finite support relevant to a specified interface or allowed gate set. -/
def flagGateSupport (A : Set (X.obj (op ⦋0⦌))) (x : (flagHom X a b).obj q) :
    Set (X.obj (op ⦋0⦌)) := A ∩ flagVertexSupport x

theorem flagGateSupport_finite (A : Set (X.obj (op ⦋0⦌))) (x : (flagHom X a b).obj q) :
    (flagGateSupport A x).Finite :=
  (flagVertexSupport_finite x).subset Set.inter_subset_right

theorem flagGateSupport_operator (A : Set (X.obj (op ⦋0⦌))) (α : q ⟶ r)
    (x : (flagHom X a b).obj q) :
    flagGateSupport A x ⊆ flagGateSupport A ((flagHom X a b).map α x) :=
  Set.inter_subset_inter_right A (flagVertexSupport_operator α x)

/-- The support is the largest allowed gate set whose subcomplex contains the supplied simplex. -/
theorem flagGateSubcomplex_mem_iff (A S : Set (X.obj (op ⦋0⦌)))
    (hSA : S ⊆ A) (x : (flagHom X a b).obj q) :
    x ∈ (flagGateSubcomplex a b S).obj q ↔ S ⊆ flagGateSupport A x := by
  exact ⟨fun h ↦ Set.subset_inter hSA h, fun h ↦ h.trans Set.inter_subset_right⟩

end

end DaggerOriginalProductGadget
