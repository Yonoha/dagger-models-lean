import OriginalFlagGateDiagram

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {A : Set (X.obj (op ⦋0⦌))}
  {R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop} {q : SimplexCategoryᵒᵖ}

/-- All nonempty subsets of the whole support, with reverse inclusion as arrows. -/
def FlagSupportSubset (x : (flagHom X a b).obj q) :=
  OrderDual {S : Set (X.obj (op ⦋0⦌)) // S.Nonempty ∧ S ⊆ flagGateSupport A x}

instance flagSupportSubsetPartialOrder (x : (flagHom X a b).obj q) :
    PartialOrder (FlagSupportSubset (A := A) x) :=
  inferInstanceAs (PartialOrder (OrderDual {S : Set (X.obj (op ⦋0⦌)) //
    S.Nonempty ∧ S ⊆ flagGateSupport A x}))

variable (x : (flagHom X a b).obj q)

/-- Forget the simplex proof in the actual augmentation fiber, retaining every gate. -/
def flagGateFiberToSupport :
    FlagGateRowFiber (A := A) (R := R) x ⥤ FlagSupportSubset (A := A) x where
  obj p := ⟨p.obj.1.val, p.obj.1.property.2.2.1, by
    apply Set.subset_inter p.obj.1.property.1
    have h := p.obj.2.property
    change p.obj.1.val ⊆ flagVertexSupport p.obj.2.val at h
    rw [flagGateRowFiber_value x p] at h
    exact h⟩
  map f := homOfLE (leOfHom f.hom.val)

/-- Insert the supplied original simplex into each support subset. Finiteness and the chain
condition are inherited from its whole support, not added to the subset index. -/
def flagSupportToGateFiber (hx : IsChain R (flagGateSupport A x)) :
    FlagSupportSubset (A := A) x ⥤ FlagGateRowFiber (A := A) (R := R) x where
  obj S := ⟨⟨⟨S.val, S.property.2.trans Set.inter_subset_left,
    (flagGateSupport_finite A x).subset S.property.2, S.property.1,
    IsChain.mono S.property.2 hx⟩,
    ⟨x, S.property.2.trans Set.inter_subset_right⟩⟩, rfl⟩
  map f := ObjectProperty.homMk ⟨homOfLE (leOfHom f), Subtype.ext rfl⟩

theorem flagGateFiberToSupport_obj_val (p : FlagGateRowFiber (A := A) (R := R) x) :
    ((flagGateFiberToSupport x).obj p).val = p.obj.1.val := rfl

theorem flagSupportToGateFiber_obj_value (hx : IsChain R (flagGateSupport A x))
    (S : FlagSupportSubset (A := A) x) :
    ((flagSupportToGateFiber x hx).obj S).obj.2.val = x := rfl

/-- The two actual functors are inverse on the entire support-subset category. -/
theorem flagSupport_fiber_roundtrip (hx : IsChain R (flagGateSupport A x)) :
    flagSupportToGateFiber x hx ⋙ flagGateFiberToSupport x = 𝟭 _ := by
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The reverse round trip also retains the original simplex, not merely its index. -/
theorem flagGate_fiber_roundtrip (hx : IsChain R (flagGateSupport A x)) :
    flagGateFiberToSupport x ⋙ flagSupportToGateFiber x hx = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun p ↦ ?_)
  rcases p with ⟨⟨S, ⟨z, hz⟩⟩, hp⟩
  have he : z = x := congrArg Discrete.as hp
  subst z
  rfl

/-- The whole nonempty support is an actual initial object of its subset category. -/
def flagSupportInitialObj (hne : (flagGateSupport A x).Nonempty) :
    FlagSupportSubset (A := A) x := ⟨flagGateSupport A x, hne, Set.Subset.rfl⟩

def flagSupportIsInitial (hne : (flagGateSupport A x).Nonempty) :
    IsInitial (flagSupportInitialObj x hne) :=
  IsInitial.ofUniqueHom (fun S ↦ homOfLE S.property.2) (fun _ _ ↦ Subsingleton.elim _ _)

end

end DaggerOriginalProductGadget
