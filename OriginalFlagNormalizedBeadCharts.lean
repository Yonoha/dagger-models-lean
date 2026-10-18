import OriginalFlagNormalizationJointImages

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

theorem stdDimensionTransport_vertex {m n : ℕ} (h : m = n) (v : Fin (m + 1)) :
    SSet.stdSimplex.obj₀Equiv
      ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h)).app (op ⦋0⦌)
        (SSet.stdSimplex.obj₀Equiv.symm v)) =
      Fin.castOrderIso (congrArg (fun k : ℕ ↦ k + 1) h) v := by
  subst n
  change SSet.stdSimplex.obj₀Equiv.{u} (SSet.stdSimplex.obj₀Equiv.{u}.symm v) = v
  exact SSet.stdSimplex.obj₀Equiv.{u}.apply_symm_apply v

theorem stdDimensionTransport_trans {l m n : ℕ} (h : l = m) (g : m = n) :
    eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h) ≫
      eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) g) =
        eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) (h.trans g)) := by
  subst m
  subst n
  rfl

theorem wedgeLeftBead_length (T U : NecklaceCode) (c : T.Bead) :
    (wedgeLeftBead T U c).length = c.length := by
  simp only [Bead.length, Bead.interval, Fin.card_Icc, wedgeLeftBead, wedgeLeft]
  change c.right.val + 1 - c.left.val - 1 = c.right.val + 1 - c.left.val - 1
  rfl

theorem wedgeRightBead_length (T U : NecklaceCode) (c : U.Bead) :
    (wedgeRightBead T U c).length = c.length := by
  have h := c.lt
  simp only [Fin.lt_def] at h
  simp only [Bead.length, Bead.interval, Fin.card_Icc, wedgeRightBead, wedgeRight]
  change (T.len + c.right.val) + 1 - (T.len + c.left.val) - 1 =
    c.right.val + 1 - c.left.val - 1
  omega

/-- Full original simplex chart, including the original dimension transport and wedge leg. -/
theorem wedgeLeftBead_chart (T U : NecklaceCode) (c : T.Bead) :
    (wedge T U).beadSimplex (wedgeLeftBead T U c) =
      eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) (wedgeLeftBead_length T U c)) ≫
        T.beadSimplex c ≫ wedgeιLeft T U := by
  apply (cancel_mono (wedge T U).inclusion).1
  apply stdSimplex_hom_ext
  intro z
  apply SSet.stdSimplex.obj₀Equiv.injective
  let v := SSet.stdSimplex.obj₀Equiv z
  have hz : z = SSet.stdSimplex.obj₀Equiv.symm v :=
    (SSet.stdSimplex.obj₀Equiv.symm_apply_apply z).symm
  let h := wedgeLeftBead_length T U c
  let w := Fin.castOrderIso (congrArg (fun k : ℕ ↦ k + 1) h) v
  have hs : (eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h)).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm v) = SSet.stdSimplex.obj₀Equiv.symm w := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rw [stdDimensionTransport_vertex h v, SSet.stdSimplex.obj₀Equiv.apply_symm_apply]
  change ((wedge T U).verticesEquiv
    ((wedge T U).beadSimplex (wedgeLeftBead T U c) |>.app _ z)).down =
      ((wedge T U).verticesEquiv ((wedgeιLeft T U).app _
        (T.beadSimplex c |>.app _
          ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h)).app _ z)))).down
  rw [hz, (wedgeLeftBead T U c).beadSimplex_vertex, hs]
  rw [← T.verticesEquiv.symm_apply_apply
    (T.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm w))]
  change (wedgeLeftBead T U c).embedding v =
    (mapVertices (wedgeιLeft T U)
      (T.verticesEquiv (T.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm w)))).down
  rw [c.beadSimplex_vertex, wedgeιLeft_vertices]
  apply Fin.ext
  rw [bead_embedding_val]
  change c.left.val + v.val = (c.embedding w).val
  rw [bead_embedding_val]
  rfl

theorem wedgeRightBead_chart (T U : NecklaceCode) (c : U.Bead) :
    (wedge T U).beadSimplex (wedgeRightBead T U c) =
      eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) (wedgeRightBead_length T U c)) ≫
        U.beadSimplex c ≫ wedgeιRight T U := by
  apply (cancel_mono (wedge T U).inclusion).1
  apply stdSimplex_hom_ext
  intro z
  apply SSet.stdSimplex.obj₀Equiv.injective
  let v := SSet.stdSimplex.obj₀Equiv z
  have hz : z = SSet.stdSimplex.obj₀Equiv.symm v :=
    (SSet.stdSimplex.obj₀Equiv.symm_apply_apply z).symm
  let h := wedgeRightBead_length T U c
  let w := Fin.castOrderIso (congrArg (fun k : ℕ ↦ k + 1) h) v
  have hs : (eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h)).app (op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm v) = SSet.stdSimplex.obj₀Equiv.symm w := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    rw [stdDimensionTransport_vertex h v, SSet.stdSimplex.obj₀Equiv.apply_symm_apply]
  change ((wedge T U).verticesEquiv
    ((wedge T U).beadSimplex (wedgeRightBead T U c) |>.app _ z)).down =
      ((wedge T U).verticesEquiv ((wedgeιRight T U).app _
        (U.beadSimplex c |>.app _
          ((eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h)).app _ z)))).down
  rw [hz, (wedgeRightBead T U c).beadSimplex_vertex, hs]
  rw [← U.verticesEquiv.symm_apply_apply
    (U.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm w))]
  change (wedgeRightBead T U c).embedding v =
    (mapVertices (wedgeιRight T U)
      (U.verticesEquiv (U.beadSimplex c |>.app _ (SSet.stdSimplex.obj₀Equiv.symm w)))).down
  rw [c.beadSimplex_vertex, wedgeιRight_vertices]
  apply Fin.ext
  rw [bead_embedding_val]
  change (T.len + c.left.val) + v.val = T.len + (c.embedding w).val
  rw [bead_embedding_val]
  change T.len + c.left.val + v.val = T.len + (c.left.val + w.val)
  have hw : w.val = v.val := rfl
  omega

theorem singleBead_left {n : ℕ} (c : (single n).Bead) : c.left = 0 := by
  rcases (mem_single_joints n c.left).mp c.left_mem with h | h
  · exact h
  · exact False.elim ((not_lt_of_ge (Fin.le_last c.right)) (h ▸ c.lt))

theorem singleBead_right {n : ℕ} (c : (single n).Bead) : c.right = Fin.last n := by
  rcases (mem_single_joints n c.right).mp c.right_mem with h | h
  · exact False.elim ((not_lt_of_ge (Fin.zero_le c.left)) (h ▸ c.lt))
  · exact h

theorem singleBead_length {n : ℕ} (c : (single n).Bead) : c.length = n := by
  simp only [Bead.length, Bead.interval, Fin.card_Icc, singleBead_left, singleBead_right]
  change n + 1 - 0 - 1 = n
  omega

theorem singleBead_chart {n : ℕ} (c : (single n).Bead) :
    (single n).beadSimplex c ≫ (singleIso n).hom =
      eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) (singleBead_length c)) := by
  apply stdSimplex_hom_ext
  intro z
  apply SSet.stdSimplex.obj₀Equiv.injective
  let v := SSet.stdSimplex.obj₀Equiv z
  have hz : z = SSet.stdSimplex.obj₀Equiv.symm v :=
    (SSet.stdSimplex.obj₀Equiv.symm_apply_apply z).symm
  change SSet.stdSimplex.obj₀Equiv
    ((singleIso n).hom.app _ ((single n).beadSimplex c |>.app _ z)) = _
  rw [singleIso_vertex, hz, c.beadSimplex_vertex,
    stdDimensionTransport_vertex (singleBead_length c) v]
  apply Fin.ext
  rw [bead_embedding_val, singleBead_left]
  change 0 + v.val = v.val
  omega

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem nonDegenerate_dim_transport {m n : ℕ} (h : m = n) (f : (Δ[n] : SSet.{u}) ⟶ X)
    (hf : SSet.yonedaEquiv f ∈ X.nonDegenerate n) :
    SSet.yonedaEquiv (eqToHom (congrArg (fun k ↦ (Δ[k] : SSet.{u})) h) ≫ f) ∈
      X.nonDegenerate m := by
  subst n
  simpa only [eqToHom_refl, Category.id_comp] using hf

/-- Every positive surviving bead has a SAME original index and a whole chosen EZ chart. -/
theorem orderedPrefix_bead_chart (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) (c : (orderedPrefix P k hk).normalized.code.Bead) :
    ∃ i : Fin (beadCount P.code), i.val < k ∧
      ∃ h : c.length = (normalizeBead P (jointBead P.code i)).dim,
        (orderedPrefix P k hk).normalized.code.beadSimplex c ≫
          (orderedPrefix P k hk).normalized.map =
            eqToHom (congrArg (fun n ↦ (Δ[n] : SSet.{u})) h) ≫
              SSet.yonedaEquiv.symm (normalizeBead P (jointBead P.code i)).simplex.val := by
  induction k with
  | zero =>
    have h := c.lt
    have hl := c.left.isLt
    have hr := c.right.isLt
    change c.left.val < c.right.val at h
    change c.left.val < 1 at hl
    change c.right.val < 1 at hr
    omega
  | succ k ih =>
    let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
    let i : Fin (beadCount P.code) := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    let d := normalizeBead P (jointBead P.code i)
    let Q := (orderedPrefix P k hp).normalized
    let V := normalizedBeadOver P (jointBead P.code i) d
    rcases wedge_bead_cases Q.code V.code c with ⟨e, he⟩ | ⟨e, he⟩
    · subst c
      obtain ⟨j, hj, hdim, hchart⟩ := ih hp e
      refine ⟨j, hj.trans (Nat.lt_succ_self k),
        (wedgeLeftBead_length Q.code V.code e).trans hdim, ?_⟩
      change (wedge Q.code V.code).beadSimplex (wedgeLeftBead Q.code V.code e) ≫
        (NecklacesOver.wedge Q V).map = _
      rw [wedgeLeftBead_chart]
      simp only [Category.assoc]
      rw [NecklacesOver.wedge_left, hchart]
      rw [← Category.assoc,
        stdDimensionTransport_trans (wedgeLeftBead_length Q.code V.code e) hdim]
    · subst c
      refine ⟨i, Nat.lt_succ_self k,
        (wedgeRightBead_length Q.code V.code e).trans (singleBead_length e), ?_⟩
      change (wedge Q.code V.code).beadSimplex (wedgeRightBead Q.code V.code e) ≫
        (NecklacesOver.wedge Q V).map = _
      rw [wedgeRightBead_chart]
      simp only [Category.assoc]
      rw [NecklacesOver.wedge_right]
      dsimp only [V, normalizedBeadOver]
      rw [← Category.assoc ((single d.dim).beadSimplex e), singleBead_chart e,
        ← Category.assoc,
        stdDimensionTransport_trans (wedgeRightBead_length Q.code V.code e)
          (singleBead_length e)]

theorem normOver_bead_chart (P : NecklacesOver X a b) (c : (normOver P).code.Bead) :
    ∃ i : Fin (beadCount P.code),
      ∃ h : c.length = (normalizeBead P (jointBead P.code i)).dim,
        (normOver P).code.beadSimplex c ≫ (normOver P).map =
          eqToHom (congrArg (fun n ↦ (Δ[n] : SSet.{u})) h) ≫
            SSet.yonedaEquiv.symm (normalizeBead P (jointBead P.code i)).simplex.val := by
  obtain ⟨i, _hi, hdim, hchart⟩ := orderedPrefix_bead_chart P _ _ c
  exact ⟨i, hdim, hchart⟩

/-- Actual beadElement of SAME normOver P is ND; no Mono of its map into X is inferred. -/
theorem normOver_beads_nondegenerate (P : NecklacesOver X a b) (c : (normOver P).code.Bead) :
    beadElement (normOver P) c ∈ X.nonDegenerate c.length := by
  obtain ⟨i, hdim, hchart⟩ := normOver_bead_chart P c
  change SSet.yonedaEquiv ((normOver P).code.beadSimplex c ≫ (normOver P).map) ∈ _
  rw [hchart]
  apply nonDegenerate_dim_transport hdim
  rw [SSet.yonedaEquiv.apply_symm_apply]
  exact (normalizeBead P (jointBead P.code i)).simplex.property

end

end DaggerOriginalFlagFlankification
