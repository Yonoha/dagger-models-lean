import DaggerModels.DegreewisePushout
import DaggerModels.FreeCofibrationCoproduct

/-!
# Coproduct attachment squares

The cells in one relative skeletal step all have the same dimension.
This packages the degreewise intersection and complement criteria for a
coproduct of copies of one genuine free cofibration. The maps from the
individual cells into the target are not assumed monic.
-/

open CategoryTheory Limits Simplicial Opposite

universe u

namespace DaggerModels.DaggerSSet

local instance : HasColimits DaggerSSet.{u} := daggerSSetHasColimits

variable {R : Type u} {A B X Y : DaggerSSet.{u}}

theorem sigma_map_hom_app (g : A ⟶ B) (r : R) (k : SimplexCategoryᵒᵖ)
    (x : A.toSSet.obj k) :
    (Limits.Sigma.map (fun _ : R ↦ g)).hom.app k
        ((Sigma.ι (fun _ : R ↦ A) r).hom.app k x) =
      (Sigma.ι (fun _ : R ↦ B) r).hom.app k (g.hom.app k x) :=
  congrArg (fun f : A ⟶ ∐ (fun _ : R ↦ B) ↦ f.hom.app k x)
    (Sigma.ι_map (fun _ : R ↦ g) r)

theorem sigma_desc_hom_app (b : R → (B ⟶ Y)) (r : R) (k : SimplexCategoryᵒᵖ)
    (x : B.toSSet.obj k) :
    (Sigma.desc b).hom.app k ((Sigma.ι (fun _ : R ↦ B) r).hom.app k x) =
      (b r).hom.app k x :=
  congrArg (fun f : B ⟶ Y ↦ f.hom.app k x) (Sigma.ι_desc b r)

/-- A simplex in a specified summand belongs to the coproduct image exactly
when its representative belongs to the original map's image. -/
theorem sigma_ι_mem_range_sigma_map_iff (g : A ⟶ B) (r : R)
    (k : SimplexCategoryᵒᵖ) (x : B.toSSet.obj k) :
    (Sigma.ι (fun _ : R ↦ B) r).hom.app k x ∈
        Set.range ((Limits.Sigma.map (fun _ : R ↦ g)).hom.app k) ↔
      x ∈ Set.range (g.hom.app k) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit
      (isColimit_cofan_hom_app (Sigma.ι (fun _ : R ↦ A))
        (coproductIsCoproduct _) k) a
    change (Limits.Sigma.map (fun _ : R ↦ g)).hom.app k
      ((Sigma.ι (fun _ : R ↦ A) s).hom.app k y) =
        (Sigma.ι (fun _ : R ↦ B) r).hom.app k x at ha
    rw [sigma_map_hom_app] at ha
    obtain rfl := Cofan.eq_of_inj_apply_eq_of_isColimit
      (isColimit_cofan_hom_app (Sigma.ι (fun _ : R ↦ B))
        (coproductIsCoproduct _) k) _ _ ha
    exact ⟨y, Cofan.inj_injective_of_isColimit
      (isColimit_cofan_hom_app (Sigma.ι (fun _ : R ↦ B))
        (coproductIsCoproduct _) k) s ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(Sigma.ι (fun _ : R ↦ A) r).hom.app k a, sigma_map_hom_app g r k a⟩

/-- The actual coproduct square is a pushout when the new simplices have
precisely the prescribed boundary, coverage, and uniqueness properties. -/
theorem isPushout_coproduct_of_complement (g : A ⟶ B) (hg : FreeCofibration g)
    (f : X ⟶ Y) [Mono f] (a : R → (A ⟶ X)) (b : R → (B ⟶ Y))
    (w : ∀ r, a r ≫ f = g ≫ b r)
    (hpre : ∀ r k (x : B.toSSet.obj k),
      (b r).hom.app k x ∈ Set.range (f.hom.app k) → x ∈ Set.range (g.hom.app k))
    (hcover : ∀ k (x : Y.toSSet.obj k),
      x ∈ Set.range (f.hom.app k) ∨ ∃ r y, (b r).hom.app k y = x)
    (hinj : ∀ r s k (x y : B.toSSet.obj k),
      x ∉ Set.range (g.hom.app k) → y ∉ Set.range (g.hom.app k) →
      (b r).hom.app k x = (b s).hom.app k y → r = s ∧ x = y) :
    IsPushout (Sigma.desc a) (Limits.Sigma.map (fun _ : R ↦ g)) f (Sigma.desc b) := by
  let : Mono (Limits.Sigma.map (fun _ : R ↦ g)) :=
    (FreeCofibration.sigma_map (fun _ : R ↦ g) (fun _ ↦ hg)).1
  apply isPushout_of_degreewise_complement
  · apply Sigma.hom_ext
    intro r
    simp only [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_desc]
    exact w r
  · intro k x hx
    obtain ⟨r, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit
      (isColimit_cofan_hom_app (Sigma.ι (fun _ : R ↦ B))
        (coproductIsCoproduct _) k) x
    change (Sigma.desc b).hom.app k
      ((Sigma.ι (fun _ : R ↦ B) r).hom.app k y) ∈ Set.range (f.hom.app k) at hx
    rw [sigma_desc_hom_app] at hx
    exact (sigma_ι_mem_range_sigma_map_iff g r k y).2 (hpre r k y hx)
  · intro k x
    obtain h | ⟨r, y, hy⟩ := hcover k x
    · exact Or.inl h
    · exact Or.inr ⟨(Sigma.ι (fun _ : R ↦ B) r).hom.app k y,
        (sigma_desc_hom_app b r k y).trans hy⟩
  · intro k x y hx hy he
    obtain ⟨r, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit
      (isColimit_cofan_hom_app (Sigma.ι (fun _ : R ↦ B))
        (coproductIsCoproduct _) k) x
    obtain ⟨s, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit
      (isColimit_cofan_hom_app (Sigma.ι (fun _ : R ↦ B))
        (coproductIsCoproduct _) k) y
    change (Sigma.desc b).hom.app k ((Sigma.ι (fun _ : R ↦ B) r).hom.app k x) =
      (Sigma.desc b).hom.app k ((Sigma.ι (fun _ : R ↦ B) s).hom.app k y) at he
    rw [sigma_desc_hom_app, sigma_desc_hom_app] at he
    have hx' := fun h ↦ hx ((sigma_ι_mem_range_sigma_map_iff g r k x).2 h)
    have hy' := fun h ↦ hy ((sigma_ι_mem_range_sigma_map_iff g s k y).2 h)
    obtain ⟨rfl, rfl⟩ := hinj r s k x y hx' hy' he
    rfl

end DaggerModels.DaggerSSet
