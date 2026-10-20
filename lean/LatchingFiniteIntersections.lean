import LatchingEZMembership
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.EqToHom

/-!
Source-only candidate: actual finite intersections and the original toRange isomorphism.
All degrees, empty index sets and both whole inverse maps are retained. No Lean call yet.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerBisimplicialDiagonal

abbrev outerAt (B : SimplicialObject SSet.{u}) (q : SimplexCategoryᵒᵖ) : SSet.{u} :=
  B.flip.obj q

def degeneracyRange (B : SimplicialObject SSet.{u}) :
    (n : ℕ) → Fin n → (B.obj (op ⦋n⦌)).Subcomplex
  | 0, i => Fin.elim0 i
  | _n + 1, i => SSet.Subcomplex.range (B.σ i)

def finiteIntersection (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) : (B.obj (op ⦋n⦌)).Subcomplex :=
  ⨅ i : Fin n, ⨅ (_ : i ∈ I), degeneracyRange B n i

theorem finiteIntersection_empty (B : SimplicialObject SSet.{u}) (n : ℕ) :
    finiteIntersection B n ∅ = ⊤ := by
  simp [finiteIntersection]

theorem finiteIntersection_zero (B : SimplicialObject SSet.{u}) (I : Finset (Fin 0)) :
    finiteIntersection B 0 I = ⊤ := by
  have hI : I = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ ↦ Fin.elim0 i)
  rw [hI, finiteIntersection_empty]

theorem finiteIntersection_mem_succ (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin (n + 1))) (q : SimplexCategoryᵒᵖ)
    (x : (B.obj (op ⦋n + 1⦌)).obj q) :
    x ∈ (finiteIntersection B (n + 1) I).obj q ↔
      ∀ i ∈ I, x ∈ Set.range ((B.σ i).app q) := by
  simp only [finiteIntersection, Subfunctor.iInf_obj, Set.mem_iInter]
  constructor
  · intro hx i hi
    have h := hx i
    rw [iInf_pos hi] at h
    exact h
  · intro hx i
    by_cases hi : i ∈ I
    · rw [iInf_pos hi]
      exact hx i hi
    · rw [iInf_neg hi]
      exact Set.mem_univ x

theorem finiteIntersection_eq_range (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) :
    finiteIntersection B n I = SSet.Subcomplex.range (B.map (rho I).op) := by
  cases n with
  | zero =>
      have hI : I = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ ↦ Fin.elim0 i)
      subst I
      rw [finiteIntersection_empty, rho_empty, op_id]
      change (⊤ : (B.obj (op ⦋0⦌)).Subcomplex) =
        Subfunctor.range (B.map (𝟙 (op ⦋0⦌)))
      rw [B.map_id]
      exact (Subfunctor.range_id (B.obj (op ⦋0⦌))).symm
  | succ n =>
      ext q x
      rw [finiteIntersection_mem_succ]
      obtain ⟨m, f, hf, y, hxy⟩ := (outerAt B q).exists_nonDegenerate x
      letI : Epi f := hf
      change (∀ i ∈ I, x ∈ Set.range ((outerAt B q).σ i)) ↔
        x ∈ Set.range ((outerAt B q).map (rho I).op)
      rw [mem_rho_range_iff_ez_collapses (outerAt B q) I x f y hxy]
      constructor
      · intro hx i hi
        exact (mem_sigma_range_iff_ez_collapse (outerAt B q) x f y hxy i).mp (hx i hi)
      · intro hx i hi
        exact (mem_sigma_range_iff_ez_collapse (outerAt B q) x f y hxy i).mpr (hx i hi)

private theorem eqToHom_subcomplex_ι {X : SSet.{u}} {A D : X.Subcomplex} (h : A = D) :
    eqToHom (congrArg SSet.Subcomplex.toSSet h) ≫ D.ι = A.ι := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

noncomputable def intersectionIso (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) :
    B.obj (op ⦋n - I.card⦌) ≅ (finiteIntersection B n I : SSet.{u}) :=
  letI := rho_isSplitEpi I
  asIso (SSet.Subcomplex.toRange (B.map (rho I).op)) ≪≫
    eqToIso (congrArg SSet.Subcomplex.toSSet (finiteIntersection_eq_range B n I).symm)

theorem intersectionIso_hom_ι (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) :
    (intersectionIso B n I).hom ≫ (finiteIntersection B n I).ι = B.map (rho I).op := by
  letI := rho_isSplitEpi I
  change (SSet.Subcomplex.toRange (B.map (rho I).op) ≫
    eqToHom (congrArg SSet.Subcomplex.toSSet (finiteIntersection_eq_range B n I).symm)) ≫
      (finiteIntersection B n I).ι = B.map (rho I).op
  rw [Category.assoc, eqToHom_subcomplex_ι (finiteIntersection_eq_range B n I).symm]
  exact SSet.Subcomplex.toRange_ι (B.map (rho I).op)

theorem intersectionIso_inv_formula (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) :
    (intersectionIso B n I).inv =
      letI := rho_isSplitEpi I
      (finiteIntersection B n I).ι ≫ B.map (section_ (rho I)).op := by
  letI := rho_isSplitEpi I
  symm
  apply (intersectionIso B n I).hom_comp_eq_id.mp
  rw [← Category.assoc, intersectionIso_hom_ι, ← B.map_comp, ← op_comp,
    IsSplitEpi.id, op_id, B.map_id]

theorem intersectionIso_hom_inv (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) :
    (intersectionIso B n I).hom ≫ (intersectionIso B n I).inv =
      𝟙 (B.obj (op ⦋n - I.card⦌)) :=
  (intersectionIso B n I).hom_inv_id

theorem intersectionIso_inv_hom (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) :
    (intersectionIso B n I).inv ≫ (intersectionIso B n I).hom =
      𝟙 (finiteIntersection B n I : SSet.{u}) :=
  (intersectionIso B n I).inv_hom_id

theorem intersectionIso_hom_operator (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (B.obj (op ⦋n - I.card⦌)).map beta ≫ (intersectionIso B n I).hom.app r =
      (intersectionIso B n I).hom.app q ≫ (finiteIntersection B n I : SSet.{u}).map beta :=
  (intersectionIso B n I).hom.naturality beta

theorem intersectionIso_inv_operator (B : SimplicialObject SSet.{u}) (n : ℕ)
    (I : Finset (Fin n)) {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (finiteIntersection B n I : SSet.{u}).map beta ≫ (intersectionIso B n I).inv.app r =
      (intersectionIso B n I).inv.app q ≫ (B.obj (op ⦋n - I.card⦌)).map beta :=
  (intersectionIso B n I).inv.naturality beta

end DaggerBisimplicialDiagonal
