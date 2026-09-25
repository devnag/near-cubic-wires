import Proof.Packets.PacketsCombineThrStage
import Proof.Packets.PacketsRowGood

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NormalizedFiniteTransport Theorem25Completion.CycleBounds
noncomputable section

variable {a : DecompositionAlgorithm}

/-- `smallSize ≤ 2^w` and `pop + 2 ≤ smallSize`. -/
theorem small_facts (K : KitShape a) (r : Request) :
    r.smallSize a ≤ 2 ^ K.w r ∧ (r.family a).occurrences.length + 2 ≤ r.smallSize a ∧
      ((r.family a).occurrences.length + 2) ^ 3 ≤ 2 ^ K.w r := by
  have h1 := RCFive.PacketBounds.positive a r
  have h12 : r.smallSize a ≤ r.smallSize a ^ 12 := Nat.le_self_pow (by norm_num) _
  have hc := K.census r
  have hp := RCFive.PacketBounds.occurrence_power a r
  have hp1 : (r.family a).occurrences.length + 2 ≤ ((r.family a).occurrences.length + 2) ^ (r.degree a + 1) :=
    Nat.le_self_pow (by omega) _
  refine ⟨h12.trans hc, hp1.trans hp, ?_⟩
  have h3 : ((r.family a).occurrences.length + 2) ^ 3 ≤ (r.smallSize a) ^ 3 :=
    Nat.pow_le_pow_left (hp1.trans hp) 3
  have h312 : (r.smallSize a) ^ 3 ≤ (r.smallSize a) ^ 12 := Nat.pow_le_pow_right h1 (by norm_num)
  exact h3.trans (h312.trans hc)

/-- A census at the request degree fits the kit width. -/
theorem census_deg (K : KitShape a) (r : Request) (e : ℕ) (he : e ≤ r.degree a) :
    ((r.family a).occurrences.length + 1) ^ e ≤ 2 ^ K.w r := by
  have hp := RCFive.PacketBounds.occurrence_power a r
  have h1 : ((r.family a).occurrences.length + 1) ^ e ≤ ((r.family a).occurrences.length + 2) ^ e :=
    Nat.pow_le_pow_left (by omega) e
  have h2 : ((r.family a).occurrences.length + 2) ^ e ≤ ((r.family a).occurrences.length + 2) ^ (r.degree a + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact h1.trans (h2.trans (hp.trans (small_facts K r).1))

theorem pop_lt_C (K : KitShape a) (r : Request) : (r.family a).occurrences.length < K.C r := by
  have h := K.codes r
  unfold codeNeed at h
  omega

/-- **SYM capacity, proved.** -/
theorem symCap (K : KitShape a) : SymCap K := by
  intro r four L target k hk
  have hdeg : r.circuits.length * Packets.coordinateDegree (symmetricFourfoldOccurrences r)
      (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) ≤
      (Request.sym r four L target).degree a :=
    RCFive.PacketBounds.degree_bound a _ _ (decode_mem a (.sym r four L target) k hk)
  have hsf := small_facts K (.sym r four L target)
  have hpop := pop_lt_C K (.sym r four L target)
  refine ⟨Finset.range (symmetricFourfoldOccurrences r).length,
    if r.circuits.length = 0 then 0 else Packets.coordinateDegree (symmetricFourfoldOccurrences r)
      (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target), ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have := Finset.mem_range.mp hj
    exact lt_trans this hpop
  · intro P hP
    rw [sym_coords_flat] at hP
    obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hPl
    refine ⟨RowGood.coord_good _ _ _ _ _ c, ?_⟩
    have hn : r.circuits.length ≠ 0 := by have := i.isLt; omega
    rw [if_neg hn]
    exact PCJc06b3608d6d34481_Rows.coordinate_degree _ _ _ _ _ c
  · rw [Finset.card_range]
    split
    · simp only [pow_zero]; exact Nat.one_le_two_pow
    · apply census_deg K (.sym r four L target)
      have : Packets.coordinateDegree (symmetricFourfoldOccurrences r)
          (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) ≤
          r.circuits.length * Packets.coordinateDegree (symmetricFourfoldOccurrences r)
          (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target) :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact this.trans hdeg
  · rw [Finset.card_range]
    split
    · simp only [Nat.zero_mul, pow_zero]; exact Nat.one_le_two_pow
    · apply census_deg K (.sym r four L target)
      rw [Nat.mul_comm]
      exact hdeg
  · have h3 := hsf.2.2
    change ((symmetricFourfoldOccurrences r).length + 2) ^ 3 ≤ _ at h3
    have hcube : 4 * ((symmetricFourfoldOccurrences r).length + 2) ≤ ((symmetricFourfoldOccurrences r).length + 2) ^ 3 := by
      have h2 : 4 ≤ ((symmetricFourfoldOccurrences r).length + 2) ^ 2 := by
        have := Nat.pow_le_pow_left (show 2 ≤ (symmetricFourfoldOccurrences r).length + 2 by omega) 2
        simpa using this
      calc 4 * ((symmetricFourfoldOccurrences r).length + 2)
          ≤ ((symmetricFourfoldOccurrences r).length + 2) ^ 2 * ((symmetricFourfoldOccurrences r).length + 2) :=
            Nat.mul_le_mul_right _ h2
        _ = ((symmetricFourfoldOccurrences r).length + 2) ^ 3 := by ring
    have hm : r.circuits.length * ((symmetricFourfoldOccurrences r).length + 1) ≤
        4 * ((symmetricFourfoldOccurrences r).length + 1) := Nat.mul_le_mul_right _ four
    omega

/-- **THR capacity, proved.** -/
theorem thrCap (K : KitShape a) : ThrCap K := by
  intro r four L target k hk
  have hdeg : modulusDigitCount k.prime.val * Packets.coordinateDegree (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L) (CloseoutFinalC10ThresholdRows.listDenominator a r target) ≤
      (Request.thr r four L target).degree a :=
    RCFive.PacketBounds.degree_bound a _ _ (decode_mem a (.thr r four L target) k hk)
  have hsf := small_facts K (.thr r four L target)
  have hpop := pop_lt_C K (.thr r four L target)
  have hdig : thrD k < 2 ^ canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r target) :=
    thr_digits_lt a r L target k
  have hwalk := small_walk a (.thr r four L target)
  change 2 ^ canonicalWalkLength (CloseoutFinalC10ThresholdRows.listDenominator a r target) ≤ _ at hwalk
  have hNs : ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k + 1 ≤ (Request.thr r four L target).smallSize a := by
    have hp := (SupplierPrime.mem_primesUpTo.mp k.prime.property).2
    have hD : thrD k ≤ modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target) := by
      unfold thrD modulusDigitCount
      exact Nat.succ_le_succ (Nat.log_mono_right hp)
    have htw : Request.tupleWork a (.thr r four L target) + 1 ≤ (Request.thr r four L target).smallSize a := by
      dsimp only [Request.smallSize]
      generalize (2:ℕ) ^ (Packets.live ((Request.thr r four L target).family a)).card = livePower
      generalize (2:ℕ) ^ (canonicalWalkLength ((Request.thr r four L target).denominator a)) = walkPower
      omega
    have hN : ((thresholdFourfoldOccurrences r).length + 1) ^ thrD k ≤ Request.tupleWork a (.thr r four L target) := by
      show _ ≤ ((thresholdFourfoldOccurrences r).length + 1) ^
        modulusDigitCount (CloseoutFinalC10ThresholdRows.primeCutoff a r target)
      exact Nat.pow_le_pow_right (by omega) hD
    omega
  refine ⟨Finset.range (thresholdFourfoldOccurrences r).length,
    if thrD k = 0 then 0 else Packets.coordinateDegree (thresholdFourfoldOccurrences r)
      (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
      (CloseoutFinalC10ThresholdRows.listDenominator a r target), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have := Finset.mem_range.mp hj
    exact lt_trans this hpop
  · intro P hP
    rw [thr_coords_flat] at hP
    obtain ⟨l, hl, hPl⟩ := List.mem_flatten.mp hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hPl
    refine ⟨RowGood.coord_good _ _ _ _ _ c, ?_⟩
    have hn : thrD k ≠ 0 := by have := i.isLt; omega
    rw [if_neg hn]
    exact PCJc06b3608d6d34481_Rows.coordinate_degree _ _ _ _ _ c
  · rw [Finset.card_range]
    split
    · simp only [pow_zero]; exact Nat.one_le_two_pow
    · apply census_deg K (.thr r four L target)
      have : Packets.coordinateDegree (thresholdFourfoldOccurrences r)
          (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r target) ≤
          modulusDigitCount k.prime.val * Packets.coordinateDegree (thresholdFourfoldOccurrences r)
          (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r target) :=
        Nat.le_mul_of_pos_left _ (by unfold thrD at *; omega)
      exact this.trans hdeg
  · rw [Finset.card_range]
    split
    · simp only [Nat.zero_mul, pow_zero]; exact Nat.one_le_two_pow
    · apply census_deg K (.thr r four L target)
      rw [Nat.mul_comm]
      exact hdeg
  · -- digits·(pop+1) + 1 ≤ smallSize^2 + 1 ≤ 2^w
    have hs := hsf.2.1
    have hsw := hsf.1
    change (thresholdFourfoldOccurrences r).length + 2 ≤ _ at hs
    have h1 : thrD k * ((thresholdFourfoldOccurrences r).length + 1) + 1 ≤
        (Request.thr r four L target).smallSize a * (Request.thr r four L target).smallSize a := by
      have := Nat.mul_le_mul (le_of_lt (lt_of_lt_of_le hdig hwalk))
        (show (thresholdFourfoldOccurrences r).length + 1 ≤ (Request.thr r four L target).smallSize a - 1 by omega)
      have hpos : 2 ≤ (Request.thr r four L target).smallSize a := by omega
      have : (Request.thr r four L target).smallSize a * ((Request.thr r four L target).smallSize a - 1) + 1 ≤
          (Request.thr r four L target).smallSize a * (Request.thr r four L target).smallSize a := by
        cases h : (Request.thr r four L target).smallSize a with
        | zero => omega
        | succ s => rw [Nat.succ_sub_one]; nlinarith
      omega
    have h2 : (Request.thr r four L target).smallSize a * (Request.thr r four L target).smallSize a ≤
        2 ^ K.w (.thr r four L target) := by
      have := K.census (.thr r four L target)
      have h1' := RCFive.PacketBounds.positive a (.thr r four L target)
      have : (Request.thr r four L target).smallSize a ^ 2 ≤ (Request.thr r four L target).smallSize a ^ 12 :=
        Nat.pow_le_pow_right h1' (by norm_num)
      nlinarith
    omega
  · have := hsf.1
    omega

end
end NearCubicWires.PacketsCombine
