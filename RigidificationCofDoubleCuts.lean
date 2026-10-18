import RigidificationCofOver
import RigidificationCofExtremeBoundary

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

open SimplicialThickening

variable {J : Type u} [LinearOrder J] {i k l j : J} {q : SimplexCategoryᵒᵖ}

def middleChain (γ : (hom i j).obj q) (hk : ∀ t, k ∈ (γ.obj t).I)
    (hl : ∀ t, l ∈ (γ.obj t).I) (hkl : k ≤ l) : (hom k l).obj q :=
  splitChainLeft ⟨splitChainRight ⟨γ, hk⟩, fun t => ⟨hl t, hkl⟩⟩

theorem splitRight_double (γ : (hom i j).obj q) (hk : ∀ t, k ∈ (γ.obj t).I)
    (hl : ∀ t, l ∈ (γ.obj t).I) (hkl : k ≤ l) :
    splitChainRight ⟨γ, hk⟩ =
      (compose k l j).app q (middleChain γ hk hl hkl, splitChainRight ⟨γ, hl⟩) := by
  apply nerve.ext_of_isThin
  funext t
  apply SimplicialThickening.Path.ext
  ext x
  constructor
  · rintro ⟨hx, hkx⟩
    rcases le_total x l with h | h
    · exact Or.inl ⟨⟨hx, hkx⟩, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨⟨hx, hkx⟩, _⟩ | ⟨hx, hlx⟩)
    · exact ⟨hx, hkx⟩
    · exact ⟨hx, hkl.trans hlx⟩

theorem splitLeft_double (γ : (hom i j).obj q) (hk : ∀ t, k ∈ (γ.obj t).I)
    (hl : ∀ t, l ∈ (γ.obj t).I) (hkl : k ≤ l) :
    splitChainLeft ⟨γ, hl⟩ =
      (compose i k l).app q (splitChainLeft ⟨γ, hk⟩, middleChain γ hk hl hkl) := by
  apply nerve.ext_of_isThin
  funext t
  apply SimplicialThickening.Path.ext
  ext x
  constructor
  · rintro ⟨hx, hxl⟩
    rcases le_total x k with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨⟨hx, h⟩, hxl⟩
  · rintro (⟨hx, hxk⟩ | ⟨⟨hx, _⟩, hxl⟩)
    · exact ⟨hx, hxk.trans hkl⟩
    · exact ⟨hx, hxl⟩

end DaggerOrdinaryRigidificationCof.PathFacets

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

def leftProper (k : interior n) : ¬ ((0 : Fin (n + 2)) = 0 ∧ k.val = Fin.last (n + 1)) :=
  fun h => (ne_of_lt k.property.2) h.2

def rightProper (k : interior n) : ¬ (k.val = 0 ∧ Fin.last (n + 1) = Fin.last (n + 1)) :=
  fun h => (ne_of_gt k.property.1) h.1

def cutEvaluation (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A) (k : interior n) :
    (extremeCut.{u} n k).toSSet ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))) :=
  (cutIso (ULift.up 0) (ULift.up k.val) (ULift.up (Fin.last (n + 1)))).inv ≫
    (properMap a 0 k.val (leftProper k) ⊗ₘ
      properMap a k.val (Fin.last (n + 1)) (rightProper k)) ≫
        eComp SSet (vertex a 0) (vertex a k.val) (vertex a (Fin.last (n + 1)))

theorem cutMap_evaluation (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (k : interior n) :
    cutMap (ULift.up 0) (ULift.up k.val) (ULift.up (Fin.last (n + 1))) ≫
      cutEvaluation a k =
      (properMap a 0 k.val (leftProper k) ⊗ₘ
        properMap a k.val (Fin.last (n + 1)) (rightProper k)) ≫
          eComp SSet (vertex a 0) (vertex a k.val) (vertex a (Fin.last (n + 1))) := by
  change (cutIso _ _ _).hom ≫ ((cutIso _ _ _).inv ≫ _ ≫ _) = _
  simp only [Iso.hom_inv_id_assoc]

def elementComp {x y z : A.Obj} (q : SimplexCategoryᵒᵖ)
    (f : (x ⟶[SSet.{u}] y).obj q) (g : (y ⟶[SSet.{u}] z).obj q) :
    (x ⟶[SSet.{u}] z).obj q := (eComp SSet x y z).app q (f, g)

theorem element_assoc {w x y z : A.Obj} (q : SimplexCategoryᵒᵖ)
    (f : (w ⟶[SSet.{u}] x).obj q) (g : (x ⟶[SSet.{u}] y).obj q)
    (h : (y ⟶[SSet.{u}] z).obj q) :
    elementComp q (elementComp q f g) h = elementComp q f (elementComp q g h) := by
  exact congrFun (congrArg (fun k => k.app q) (e_assoc SSet w x y z)) (f, (g, h))

end

end DaggerOrdinaryRigidificationCof.BoundaryData
