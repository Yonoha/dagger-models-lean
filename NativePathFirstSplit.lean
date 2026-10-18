import NativePathFactorizationUniqueness

/-! Unique first-edge decompositions use the native path and the native decomposition theorem. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativePathFirstSplit
noncomputable section
open DaggerNativePathFactorizationUniqueness

variable {V : Type u} [Quiver.{u + 1} V] {a b : V}

structure FirstSplit (p : Quiver.Path a b) where
  middle : V
  first : a ⟶ middle
  rest : Quiver.Path middle b
  spec : first.toPath.comp rest = p

instance firstSplit_subsingleton (p : Quiver.Path a b) : Subsingleton (FirstSplit p) where
  allEq s t := by
    rcases s with ⟨c, e, q, hs⟩
    rcases t with ⟨c', e', q', ht⟩
    have h := split_unique_of_prefix_length e.toPath q e'.toPath q' rfl (hs.trans ht.symm)
    obtain ⟨hc, he, hq⟩ := h
    subst c'
    have he' : e = e' :=
      eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons (eq_of_heq he))
    have hq' : q = q' := eq_of_heq hq
    subst e'
    subst q'
    rfl

def firstSplit (p : Quiver.Path a b) (hp : p.length ≠ 0) : FirstSplit p :=
  Classical.choice (by
    obtain ⟨c, e, q, h, _⟩ := (Quiver.Path.length_ne_zero_iff_eq_comp p).mp hp
    exact ⟨⟨c, e, q, h.symm⟩⟩)

theorem firstSplit_eq (p : Quiver.Path a b) (hp : p.length ≠ 0) (s : FirstSplit p) :
    firstSplit p hp = s := Subsingleton.elim _ _

theorem rest_length (p : Quiver.Path a b) (s : FirstSplit p) :
    s.rest.length + 1 = p.length := by
  have h := congrArg Quiver.Path.length s.spec
  simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at h
  omega

theorem rest_positive (p : Quiver.Path a b) (s : FirstSplit p) (hp : 1 < p.length) :
    0 < s.rest.length := by
  have h := rest_length p s
  omega

theorem split_of_edge_comp {c : V} (e : a ⟶ c) (q : Quiver.Path c b)
    (hp : (e.toPath.comp q).length ≠ 0) :
    firstSplit (e.toPath.comp q) hp = ⟨c, e, q, rfl⟩ := Subsingleton.elim _ _

end
end DaggerNativePathFirstSplit
