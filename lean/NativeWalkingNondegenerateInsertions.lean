import NativeWalkingWordInsertions
import AdjacentWordInsertions

/-! Nondegenerate relative insertions are genuine uniquely indexed inner faces. -/
set_option autoImplicit false
open CategoryTheory Simplicial MonoidalCategory
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeWalkingSimplexWords
open DaggerNativeWalkingWordInsertions DaggerNativeWalkingWordFaces
universe u
namespace DaggerNativeWalkingNondegenerateInsertions
noncomputable section
variable {n d : ℕ} (x : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 1⦌)
  (i : Fin (d + 1)) (v : Fin (n + 1) × Bool)
  (hl : ((coordinates x).val i.castSucc).1 ≤ v.1)
  (hr : v.1 ≤ ((coordinates x).val i.succ).1)

def inserted : (Δ[n] ⊗ J.{u} : SSet.{u}) _⦋d + 2⦌ :=
  ofWords (insertBetween (coordinates x) i v hl hr)

theorem delta_inserted : (Δ[n] ⊗ J.{u}).δ i.succ.castSucc (inserted x i v hl hr) = x := by
  simpa only [ofWords_coordinates] using
    delta_insertWords.{u} (coordinates x) i.succ.castSucc v
      (show Monotone (fun k ↦ (Fin.insert (coordinates x).val i.succ.castSucc v k).1) from
        (insertBetween (coordinates x) i v hl hr).property)

theorem inserted_nonDegenerate
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1))
    (hln : (coordinates x).val i.castSucc ≠ v) (hrn : v ≠ (coordinates x).val i.succ) :
    inserted x i v hl hr ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 2) := by
  apply (nonDegenerate_iff (inserted x i v hl hr)).mpr
  change ∀ j : Fin (d + 2), Fin.insert (coordinates x).val i.succ.castSucc v j.castSucc ≠
    Fin.insert (coordinates x).val i.succ.castSucc v j.succ
  exact DaggerAdjacentWordInsertions.adjacentDistinct_insert (coordinates x).val
    ((nonDegenerate_iff x).mp hx) i v hln hrn

theorem inserted_relative
    (hx : x ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _) :
    inserted x i v hl hr ∉ ((SSet.boundary n).unionProd
      DaggerNativeWalkingRelativeGenerators.zeroSubcomplex.{u}).obj _ := by
  obtain ⟨hs, ht⟩ := (notMem_relative_iff x).mp hx
  exact insertWords_notMem (coordinates x) i.succ.castSucc v
    (insertBetween (coordinates x) i v hl hr).property hs ht

theorem uniquelyCodimOneFace_inserted
    (hx : x ∈ (Δ[n] ⊗ J.{u}).nonDegenerate (d + 1))
    (hln : (coordinates x).val i.castSucc ≠ v) (hrn : v ≠ (coordinates x).val i.succ) :
    SSet.IsUniquelyCodimOneFace x (inserted x i v hl hr) := by
  have hh := uniquelyCodimOneFace (inserted x i v hl hr)
    (inserted_nonDegenerate x i v hl hr hx hln hrn) i.succ.castSucc
  rwa [delta_inserted] at hh

theorem insertion_index_inner : i.succ.castSucc ≠ 0 ∧ i.succ.castSucc ≠ Fin.last (d + 2) := by
  constructor <;> intro he <;> have hv := congrArg Fin.val he
  all_goals
    simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero] at hv
    omega

end
end DaggerNativeWalkingNondegenerateInsertions
