import ActualOrdinalRigidificationComparison

/-! Full interval paths in the SAME native thickening; no simplex-naturality is asserted. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeThickeningFullPaths
noncomputable section
variable {J : Type u} [LinearOrder J]

/-- The maximal native path with the actual ordered endpoints. -/
def fullPath (i j : J) (hij : i ≤ j) : SimplicialThickening.Path i j where
  I := Set.Icc i j
  left := ⟨le_rfl, hij⟩
  right := ⟨hij, le_rfl⟩
  left_le _ h := h.1
  le_right _ h := h.2

/-- Every native path is included in the full interval with its same endpoints. -/
theorem subset_full {i j : J} (p : SimplicialThickening.Path i j) :
    p.I ⊆ (fullPath i j p.le).I := fun k hk ↦ ⟨p.left_le k hk, p.le_right k hk⟩

/-- The full path at a repeated endpoint is precisely its singleton. -/
theorem fullPath_self (i : J) : (fullPath i i le_rfl).I = {i} := Set.Icc_self i

/-- Full paths compose by the SAME union used by the original thickening. -/
theorem fullPath_union (i j k : J) (hij : i ≤ j) (hjk : j ≤ k) :
    (fullPath i j hij).I ∪ (fullPath j k hjk).I = (fullPath i k (hij.trans hjk)).I := by
  ext t
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.trans hjk⟩
    · exact ⟨hij.trans h.1, h.2⟩
  · intro h
    rcases le_total t j with hleft | hright
    · exact Or.inl ⟨h.1, hleft⟩
    · exact Or.inr ⟨hright, h.2⟩

/-- The full-path center uses the native discrete ordered-endpoint Hom. -/
def center (i j : J) : Discrete (i ⟶ j) ⥤ SimplicialThickening.Path i j where
  obj f := fullPath i j (leOfHom f.as)
  map _ := eqToHom (by congr 1)

/-- Inclusion into the full path is a natural transformation on the entire path category. -/
def idToFull (i j : J) : 𝟭 (SimplicialThickening.Path i j) ⟶
    DaggerActualOrdinalRigidificationComparison.pathCollapse i j ⋙ center i j where
  app p := InducedCategory.homMk (homOfLE (subset_full p))
  naturality _ _ _ := by
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _

end
end DaggerNativeThickeningFullPaths
