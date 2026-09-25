import Proof.SourceAssembly.AdmissionCaps

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.P1Closure

noncomputable section

/-- The uniform degree at arity `q` and live scale `L`. -/
def uniformDeg (q L : ℕ) : ℕ := q/(200*(normalizedLiveCount q L + 2))

theorem uniformDeg_le (q L : ℕ) : uniformDeg q L ≤ q := Nat.div_le_self _ _

section
variable {a : DecompositionAlgorithm} {q L : ℕ} {F : Packets.Family q L} {g : Packets.Geometry F}

/-- Every row degree of a family is below the width of any of its layouts. -/
theorem row_degree_lt_w (layout : Packets.Layout a F g) :
    ∀ row ∈ F.rows, row.degree < layout.w := by
  intro row hrow
  have h := layout.widthFromTouch g.touch row hrow
  have h2 : 2 ≤ Packets.alphabet a F := by unfold Packets.alphabet; omega
  have hp : 2^row.degree ≤ (Packets.alphabet a F)^row.degree := Nat.pow_le_pow_left h2 _
  exact (Nat.pow_lt_pow_iff_right (by decide)).mp (hp.trans_lt h)

/-- The width of any layout is at most the uniform degree. -/
theorem w_le_uniformDeg (layout : Packets.Layout a F g) : layout.w ≤ uniformDeg q L := by
  have hl := layout.load
  unfold Packets.residual at hl
  unfold uniformDeg
  rw [Nat.le_div_iff_mul_le (by positivity)]
  have : 200*(normalizedLiveCount q L + layout.w*(normalizedLiveCount q L+2)) =
      200*normalizedLiveCount q L + layout.w*(200*(normalizedLiveCount q L+2)) := by ring
  omega


/-- `|Packets.pool| = 2^K·|childList| + 1`. -/
theorem pool_length_eq :
    (Packets.pool a F g).length =
      2^(Packets.live F).card*(C10SupplierRowInput.childList a (Packets.live F) F.occurrences).length + 1 := by
  unfold Packets.pool
  rw [BinaryPool.pool_length, C10SupplierRowInput.pool_length, C10SupplierRowInput.liveList_length]

/-- `2^K ≥ q` once the live scale is positive. -/
theorem q_le_two_pow_live (hL : 1 ≤ L) : q ≤ 2^normalizedLiveCount q L := by
  unfold normalizedLiveCount
  rcases le_total q (L*logScale q) with h | h
  · rw [min_eq_left h]
    exact (Nat.lt_two_pow_self).le
  · rw [min_eq_right h]
    have h1 : q+1 ≤ 2^logScale q := succ_le_two_pow_logScale' q
    have h2 : 2^logScale q ≤ 2^(L*logScale q) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ hL)
    omega

/-- **The effective degree, exactly.** With `L ≥ 1`, `min (uniformDeg q L) |pool|` is `uniformDeg q L`
if the child list is nonempty and `min (uniformDeg q L) 1` if it is empty. -/
theorem effectiveDegree_eq (hL : 1 ≤ L) :
    min (uniformDeg q L) (Packets.pool a F g).length =
      if (C10SupplierRowInput.childList a (Packets.live F) F.occurrences).length = 0 then
        min (uniformDeg q L) 1
      else uniformDeg q L := by
  rw [pool_length_eq]
  have hcard := g.card
  split_ifs with h
  · rw [h]; simp
  · apply min_eq_left
    have hq := q_le_two_pow_live (q := q) hL
    rw [← hcard] at hq
    have hd := uniformDeg_le q L
    have hc : 1 ≤ (C10SupplierRowInput.childList a (Packets.live F) F.occurrences).length := by omega
    have := Nat.le_mul_of_pos_right (2^(Packets.live F).card) hc
    omega

end


end
end NearCubicWires.Admission
