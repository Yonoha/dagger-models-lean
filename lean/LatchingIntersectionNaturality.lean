import LatchingFiniteIntersections

/-!
Source-only candidate: restrictions of the same eta, actual set inclusions J -> I,
the original rhoFactor and both iso transports. No type-checking claim is made.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerBisimplicialDiagonal

def intersectionMap {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ)
    (I : Finset (Fin n)) :
    (finiteIntersection B n I : SSet.{u}) ⟶ (finiteIntersection B' n I : SSet.{u}) :=
  SSet.Subcomplex.lift ((finiteIntersection B n I).ι ≫ eta.app (op ⦋n⦌)) (by
    rintro q x ⟨z, rfl⟩
    change (eta.app (op ⦋n⦌)).app q z.val ∈ (finiteIntersection B' n I).obj q
    let v : (B.obj (op ⦋n⦌)).obj q := z.val
    change (eta.app (op ⦋n⦌)).app q v ∈ (finiteIntersection B' n I).obj q
    have hz : v ∈ (finiteIntersection B n I).obj q := z.property
    rw [finiteIntersection_eq_range] at hz ⊢
    obtain ⟨w, hw⟩ := hz
    refine ⟨(eta.app (op ⦋n - I.card⦌)).app q w, ?_⟩
    have h := congr_fun (congr_app (eta.naturality (rho I).op) q) w
    change (B'.map (rho I).op).app q ((eta.app (op ⦋n - I.card⦌)).app q w) =
      (eta.app (op ⦋n⦌)).app q v
    rw [← hw]
    exact h.symm)

theorem intersectionMap_app {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ)
    (I : Finset (Fin n)) (q : SimplexCategoryᵒᵖ) (x : (finiteIntersection B n I).obj q) :
    ((intersectionMap eta n I).app q x).val = (eta.app (op ⦋n⦌)).app q x.val := rfl

theorem intersectionMap_ι {B B' : SimplicialObject SSet.{u}} (eta : B ⟶ B') (n : ℕ)
    (I : Finset (Fin n)) :
    (finiteIntersection B n I).ι ≫ eta.app (op ⦋n⦌) =
      intersectionMap eta n I ≫ (finiteIntersection B' n I).ι :=
  (SSet.Subcomplex.lift_ι _ _).symm

theorem intersectionIso_naturality {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) (I : Finset (Fin n)) :
    (intersectionIso B n I).hom ≫ intersectionMap eta n I =
      eta.app (op ⦋n - I.card⦌) ≫ (intersectionIso B' n I).hom := by
  apply (cancel_mono (finiteIntersection B' n I).ι).mp
  calc
    ((intersectionIso B n I).hom ≫ intersectionMap eta n I) ≫
        (finiteIntersection B' n I).ι =
        (intersectionIso B n I).hom ≫
          ((finiteIntersection B n I).ι ≫ eta.app (op ⦋n⦌)) := by
      rw [Category.assoc, ← intersectionMap_ι]
    _ = B.map (rho I).op ≫ eta.app (op ⦋n⦌) := by
      rw [← Category.assoc, intersectionIso_hom_ι]
    _ = eta.app (op ⦋n - I.card⦌) ≫ B'.map (rho I).op := eta.naturality (rho I).op
    _ = (eta.app (op ⦋n - I.card⦌) ≫ (intersectionIso B' n I).hom) ≫
        (finiteIntersection B' n I).ι := by rw [Category.assoc, intersectionIso_hom_ι]

theorem intersectionIso_inv_naturality {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) (I : Finset (Fin n)) :
    intersectionMap eta n I ≫ (intersectionIso B' n I).inv =
      (intersectionIso B n I).inv ≫ eta.app (op ⦋n - I.card⦌) := by
  calc
    intersectionMap eta n I ≫ (intersectionIso B' n I).inv =
        (intersectionIso B n I).inv ≫
          ((intersectionIso B n I).hom ≫ intersectionMap eta n I) ≫
            (intersectionIso B' n I).inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (intersectionIso B n I).inv ≫
        (eta.app (op ⦋n - I.card⦌) ≫ (intersectionIso B' n I).hom) ≫
          (intersectionIso B' n I).inv := by rw [intersectionIso_naturality]
    _ = (intersectionIso B n I).inv ≫ eta.app (op ⦋n - I.card⦌) := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem intersectionMap_operator {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') (n : ℕ) (I : Finset (Fin n))
    {q r : SimplexCategoryᵒᵖ} (beta : q ⟶ r) :
    (finiteIntersection B n I : SSet.{u}).map beta ≫ (intersectionMap eta n I).app r =
      (intersectionMap eta n I).app q ≫ (finiteIntersection B' n I : SSet.{u}).map beta :=
  (intersectionMap eta n I).naturality beta

theorem finiteIntersection_antitone (B : SimplicialObject SSet.{u}) {n : ℕ}
    {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    finiteIntersection B n J ≤ finiteIntersection B n I := by
  intro q x hx
  simp only [finiteIntersection, Subfunctor.iInf_obj, Set.mem_iInter] at hx ⊢
  intro i
  by_cases hi : i ∈ I
  · rw [iInf_pos hi]
    have h := hx i
    rw [iInf_pos (hIJ hi)] at h
    exact h
  · rw [iInf_neg hi]
    exact Set.mem_univ x

def intersectionInclusion (B : SimplicialObject SSet.{u}) {n : ℕ}
    {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    (finiteIntersection B n J : SSet.{u}) ⟶ (finiteIntersection B n I : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (finiteIntersection_antitone B hIJ)

theorem intersectionInclusion_ι (B : SimplicialObject SSet.{u}) {n : ℕ}
    {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    intersectionInclusion B hIJ ≫ (finiteIntersection B n I).ι =
      (finiteIntersection B n J).ι :=
  SSet.Subcomplex.homOfLE_ι (finiteIntersection_antitone B hIJ)

theorem intersectionIso_inclusion (B : SimplicialObject SSet.{u}) {n : ℕ}
    {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    (intersectionIso B n J).hom ≫ intersectionInclusion B hIJ =
      B.map (rhoFactor I (rho J)).op ≫ (intersectionIso B n I).hom := by
  have hfac : rho I ≫ rhoFactor I (rho J) = rho J :=
    rhoFactor_fac I (rho J) (fun i hi ↦ (rho_adjacent_iff J i).mpr (hIJ hi))
  apply (cancel_mono (finiteIntersection B n I).ι).mp
  calc
    ((intersectionIso B n J).hom ≫ intersectionInclusion B hIJ) ≫
        (finiteIntersection B n I).ι = B.map (rho J).op := by
      rw [Category.assoc, intersectionInclusion_ι, intersectionIso_hom_ι]
    _ = B.map (rho I ≫ rhoFactor I (rho J)).op := by rw [hfac]
    _ = B.map (rhoFactor I (rho J)).op ≫ B.map (rho I).op := by
      rw [op_comp, B.map_comp]
    _ = (B.map (rhoFactor I (rho J)).op ≫ (intersectionIso B n I).hom) ≫
        (finiteIntersection B n I).ι := by rw [Category.assoc, intersectionIso_hom_ι]

theorem intersectionIso_inv_inclusion (B : SimplicialObject SSet.{u}) {n : ℕ}
    {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    intersectionInclusion B hIJ ≫ (intersectionIso B n I).inv =
      (intersectionIso B n J).inv ≫ B.map (rhoFactor I (rho J)).op := by
  calc
    intersectionInclusion B hIJ ≫ (intersectionIso B n I).inv =
        (intersectionIso B n J).inv ≫
          ((intersectionIso B n J).hom ≫ intersectionInclusion B hIJ) ≫
            (intersectionIso B n I).inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (intersectionIso B n J).inv ≫
        (B.map (rhoFactor I (rho J)).op ≫ (intersectionIso B n I).hom) ≫
          (intersectionIso B n I).inv := by rw [intersectionIso_inclusion]
    _ = (intersectionIso B n J).inv ≫ B.map (rhoFactor I (rho J)).op := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem intersectionInclusion_naturality {B B' : SimplicialObject SSet.{u}}
    (eta : B ⟶ B') {n : ℕ} {I J : Finset (Fin n)} (hIJ : I ⊆ J) :
    intersectionInclusion B hIJ ≫ intersectionMap eta n I =
      intersectionMap eta n J ≫ intersectionInclusion B' hIJ := by
  apply (cancel_mono (finiteIntersection B' n I).ι).mp
  calc
    (intersectionInclusion B hIJ ≫ intersectionMap eta n I) ≫
        (finiteIntersection B' n I).ι =
        intersectionInclusion B hIJ ≫
          ((finiteIntersection B n I).ι ≫ eta.app (op ⦋n⦌)) := by
      rw [Category.assoc, ← intersectionMap_ι]
    _ = (finiteIntersection B n J).ι ≫ eta.app (op ⦋n⦌) := by
      rw [← Category.assoc, intersectionInclusion_ι]
    _ = (intersectionMap eta n J ≫ intersectionInclusion B' hIJ) ≫
        (finiteIntersection B' n I).ι := by
      rw [Category.assoc, intersectionInclusion_ι, ← intersectionMap_ι]

end DaggerBisimplicialDiagonal
