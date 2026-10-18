import ChosenNecklaceVertices

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode)

/-- The initial point and all actual positive bead faces. -/
def pieces : Option T.Bead → (Δ[T.len] : SSet.{u}).Subcomplex
  | none => SSet.stdSimplex.face {0}
  | some b => b.face

def cover : SSet.Subcomplex.MulticoequalizerDiagram T.complex T.pieces
    (fun i j ↦ T.pieces i ⊓ T.pieces j) where
  iSup_eq := by
    apply le_antisymm
    · apply iSup_le
      rintro (_ | b)
      · exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun c : T.Bead ↦ c.face) b)
    · apply sup_le
      · exact le_iSup T.pieces none
      · apply iSup_le
        intro b
        exact le_iSup T.pieces (some b)
  eq_inf _ _ := rfl

def unionCocone := (cover.{u} T).multicofork.map SSet.Subcomplex.toSSetFunctor

def beadDiagram :=
  ((cover.{u} T).multispanIndex.map SSet.Subcomplex.toSSetFunctor).multispan

def unionIsColimit : IsColimit (unionCocone.{u} T) := (cover.{u} T).isColimit

/-- The full union UP has the original necklace, including the exceptional point, as apex. -/
def beadCocone := (unionCocone.{u} T).extend (complexIso.{u} T).inv

def beadIsColimit : IsColimit (beadCocone.{u} T) := by
  unfold beadCocone
  exact IsColimit.extendIso (s := unionCocone.{u} T)
    (complexIso.{u} T).inv (unionIsColimit.{u} T)

theorem beadCocone_pt : T.beadCocone.pt = T.toSSet := rfl

def beadDesc (s : Cocone T.beadDiagram) : T.toSSet ⟶ s.pt :=
  T.beadIsColimit.desc s

theorem beadDesc_fac (s : Cocone T.beadDiagram) (j) :
    T.beadCocone.ι.app j ≫ T.beadDesc s = s.ι.app j :=
  T.beadIsColimit.fac s j

theorem beadDesc_uniq (s : Cocone T.beadDiagram) (k : T.toSSet ⟶ s.pt)
    (hk : ∀ j, T.beadCocone.ι.app j ≫ k = s.ι.app j) : k = T.beadDesc s :=
  T.beadIsColimit.uniq s k hk

end

end DaggerChosenRigidificationNecklace.NecklaceCode
