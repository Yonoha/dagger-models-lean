import OriginalFlagSourcePrefixJoints
import OriginalFlagFlankInclusion

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem sourcePrefix_no_joint (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) (c : (orderedPrefix P k hk).source.code.Bead)
    (v : Fin (P.code.len + 1)) (hv : v ∈ P.code.joints)
    (hl : sourcePrefixEmbedding P k hk c.left < v)
    (hr : v < sourcePrefixEmbedding P k hk c.right) : False := by
  let w : Fin ((orderedPrefix P k hk).source.code.len + 1) := ⟨v.val, by
    have hright := c.right.isLt
    change v.val < c.right.val at hr
    omega⟩
  have he : sourcePrefixEmbedding P k hk w = v := Fin.ext rfl
  have hw := (sourcePrefix_joint_iff P k hk w).mpr (he.symm ▸ hv)
  exact c.no_joint w hw ((sourcePrefixEmbedding P k hk).lt_iff_lt.mp (he.symm ▸ hl))
    ((sourcePrefixEmbedding P k hk).lt_iff_lt.mp (he.symm ▸ hr))

theorem sourcePrefix_beadCondition (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    BeadImageCondition (T := (orderedPrefix P k hk).source.code) (U := P.code)
      (sourcePrefixEmbedding P k hk).toOrderHom := by
  intro c
  obtain ⟨d, hd⟩ := interval_in_original_bead P.code
    (sourcePrefixEmbedding P k hk c.left) (sourcePrefixEmbedding P k hk c.right)
    ((sourcePrefixEmbedding P k hk).strictMono c.lt) (sourcePrefix_no_joint P k hk c)
  left
  refine ⟨d, ?_⟩
  intro v hv
  obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hv
  exact hd _ (Finset.mem_Icc.mpr
    ⟨(sourcePrefixEmbedding P k hk).monotone hl, (sourcePrefixEmbedding P k hk).monotone hr⟩)

/-- The actual prefix coordinate inclusion, lifted by the existing whole-map orderLift. -/
def sourcePrefixForward (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    NecklaceCode.toSSet.{u} (orderedPrefix P k hk).source.code ⟶
      NecklaceCode.toSSet.{u} P.code :=
  orderLift (T := (orderedPrefix P k hk).source.code) (U := P.code)
    (sourcePrefixEmbedding P k hk).toOrderHom (sourcePrefix_beadCondition P k hk)

theorem sourcePrefixForward_vertices (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code)
    (v : Vertices.{u} (orderedPrefix P k hk).source.code) :
    mapVertices (sourcePrefixForward P k hk) v = ULift.up (sourcePrefixEmbedding P k hk v.down) :=
  orderLift_vertices (T := (orderedPrefix P k hk).source.code) (U := P.code)
    (sourcePrefixEmbedding P k hk).toOrderHom (sourcePrefix_beadCondition P k hk) v

theorem sourcePrefixForward_zero (P : NecklacesOver X a b) :
    sourcePrefixForward P 0 (Nat.zero_le _) = pointAt P.code (ULift.up 0) := by
  calc
    sourcePrefixForward P 0 (Nat.zero_le _) =
        pointAt NecklaceCode.point (ULift.up 0) ≫ sourcePrefixForward P 0 (Nat.zero_le _) := by
      rw [pointAt_point, Category.id_comp]
    _ = pointAt P.code
        (mapVertices (sourcePrefixForward P 0 (Nat.zero_le _)) (ULift.up 0)) :=
      pointAt_comp _ _
    _ = pointAt P.code (ULift.up 0) := by
      have hv := sourcePrefixForward_vertices P 0 (Nat.zero_le _)
        (ULift.up 0 : Vertices.{u} NecklaceCode.point)
      have he : mapVertices (sourcePrefixForward P 0 (Nat.zero_le _)) (ULift.up 0) =
          (ULift.up 0 : Vertices.{u} P.code) :=
        hv.trans (congrArg ULift.up (sourcePrefixEmbedding_first P 0 (Nat.zero_le _)))
      exact congrArg (pointAt.{u} P.code) he

theorem sourcePrefixForward_left (P : NecklacesOver X a b) (k : ℕ)
    (hk : k + 1 ≤ beadCount P.code) :
    let hp := Nat.le_of_succ_le hk
    let c := jointBead P.code ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    wedgeιLeft (orderedPrefix P k hp).source.code (sourceBeadOver P c).code ≫
      sourcePrefixForward P (k + 1) hk = sourcePrefixForward P k hp := by
  dsimp only
  apply hom_ext_vertices
  funext v
  rw [mapVertices_comp, Function.comp_apply, wedgeιLeft_vertices, sourcePrefixForward_vertices,
    sourcePrefixForward_vertices]
  exact congrArg ULift.up (Fin.ext rfl)

/-- The actual increasing bead chart is the affine original coordinate chart. -/
theorem bead_embedding_val {T : NecklaceCode} (c : T.Bead) (v : Fin (c.length + 1)) :
    (c.embedding v).val = c.left.val + v.val := by
  have hlen : c.length = c.right.val - c.left.val := by
    have hlt := c.lt
    simp only [Bead.length, Bead.interval, Fin.card_Icc]
    simp only [Fin.lt_def] at hlt
    omega
  let f : Fin (c.length + 1) ↪o Fin (T.len + 1) :=
    { toFun := fun w ↦ ⟨c.left.val + w.val, by
        have hw := w.isLt
        have hr := c.right.isLt
        have hlt := c.lt
        simp only [Fin.lt_def] at hlt
        omega⟩
      inj' := by intro w z h; apply Fin.ext; have hh := congrArg Fin.val h; dsimp at hh; omega
      map_rel_iff' := by
        intro w z
        change c.left.val + w.val ≤ c.left.val + z.val ↔ w.val ≤ z.val
        omega }
  have hf : ∀ w, f w ∈ c.interval := by
    intro w
    apply Finset.mem_Icc.mpr
    constructor
    · change c.left.val ≤ c.left.val + w.val
      omega
    · change c.left.val + w.val ≤ c.right.val
      have hw := w.isLt
      have hlt := c.lt
      simp only [Fin.lt_def] at hlt
      omega
  have he : f = c.embedding := Finset.orderEmbOfFin_unique' c.card_interval hf
  exact (congrArg (fun e : Fin (c.length + 1) ↪o Fin (T.len + 1) ↦ (e v).val) he).symm

theorem sourcePrefixForward_right (P : NecklacesOver X a b) (k : ℕ)
    (hk : k + 1 ≤ beadCount P.code) :
    let hp := Nat.le_of_succ_le hk
    let c := jointBead P.code ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    wedgeιRight (orderedPrefix P k hp).source.code (sourceBeadOver P c).code ≫
      sourcePrefixForward P (k + 1) hk = (singleIso.{u} c.length).hom ≫ P.code.beadSimplex c := by
  dsimp only
  let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
  let i : Fin (beadCount P.code) := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  let c := jointBead P.code i
  have hT : (orderedPrefix P k hp).source.code.len = c.left.val := by
    have h := sourcePrefix_len P k hp
    convert h using 1
  apply hom_ext_vertices
  funext v
  rw [mapVertices_comp, Function.comp_apply, wedgeιRight_vertices, sourcePrefixForward_vertices]
  have hs : (singleIso.{u} c.length).hom.app (op ⦋0⦌)
      ((single c.length).verticesEquiv.symm v) = SSet.stdSimplex.obj₀Equiv.symm v.down := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    have hv := singleIso_vertex.{u} c.length ((single c.length).verticesEquiv.symm v)
    simpa only [SSet.stdSimplex.obj₀Equiv.apply_symm_apply] using
      hv.trans (congrArg ULift.down ((single c.length).verticesEquiv.apply_symm_apply v))
  change _ = P.code.verticesEquiv (P.code.beadSimplex c |>.app _
    ((singleIso.{u} c.length).hom.app _ ((single c.length).verticesEquiv.symm v)))
  rw [hs]
  refine Eq.trans ?_ (NecklaceCode.Bead.beadSimplex_vertex.{u} c v.down).symm
  apply ULift.ext
  apply Fin.ext
  change (orderedPrefix P k hp).source.code.len + v.down.val = (c.embedding v.down).val
  rw [hT, bead_embedding_val]

/-- Equality into arbitrary X uses both original whole bead maps and the finite wedge UP. -/
theorem sourcePrefixForward_triangle (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    sourcePrefixForward P k hk ≫ P.map = (orderedPrefix P k hk).source.map := by
  induction k with
  | zero =>
    rw [sourcePrefixForward_zero]
    change pointAt P.code (ULift.up 0) ≫ P.map = SSet.yonedaEquiv.symm (jointVertex P 0)
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, pointAt_vertex, SSet.yonedaEquiv.apply_symm_apply]
    rw [jointVertex, jointEmbedding_first]
    rfl
  | succ k ih =>
    let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
    let c := jointBead P.code ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    change sourcePrefixForward P (k + 1) hk ≫ P.map =
      wedgeDesc (orderedPrefix P k hp).source.code (sourceBeadOver P c).code
        (orderedPrefix P k hp).source.map (sourceBeadOver P c).map
        (NecklacesOver.wedge_compat _ _)
    apply wedgeDesc_uniq
    · rw [← Category.assoc, sourcePrefixForward_left, ih hp]
    · rw [← Category.assoc, sourcePrefixForward_right]
      rfl

end

end DaggerOriginalFlagFlankification
