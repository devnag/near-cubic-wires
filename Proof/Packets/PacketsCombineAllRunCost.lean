import Proof.Packets.PacketsXWalkLiteralProducedMajorityAllRun
import Proof.Packets.WalkLiteralProducedReserveCost

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsCombine.AllRunCost
open NearCubicWires Theorem25Completion Theorem25Completion.CycleBounds
open PCJ9eff70d512234a4c_Fixed.Materializer

/-! ## The transcript-column half, in powers of `R` -/

/-- The monomial ladder used by every bound below. -/
theorem pows (R : ℕ) (hR : 1 ≤ R) :
    R ≤ R ^ 2 ∧ R ^ 2 ≤ R ^ 3 ∧ R ^ 3 ≤ R ^ 4 ∧ R ^ 4 ≤ R ^ 5 ∧ R ^ 5 ≤ R ^ 27 ∧ 1 ≤ R ^ 27 := by
  refine ⟨?_, Nat.pow_le_pow_right hR (by omega), Nat.pow_le_pow_right hR (by omega),
    Nat.pow_le_pow_right hR (by omega), Nat.pow_le_pow_right hR (by omega), Nat.one_le_pow _ _ hR⟩
  calc R = R ^ 1 := (pow_one R).symm
    _ ≤ R ^ 2 := Nat.pow_le_pow_right hR (by omega)

section Col
variable (R : ℕ) (hR : 1 ≤ R)
include hR

theorem zeroBank_le (N : ℕ) (hN : N ≤ R) : PhysicalZeroBank.budget R N ≤ 47 * R ^ 2 := by
  unfold PhysicalZeroBank.budget
  have := Nat.mul_le_mul_right (12 * R + 24) hN
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem reset_le (T c : ℕ) (hT : T ≤ R) (hc : c ≤ R) : TranscriptColumn.resetBudget R T c ≤ 52 * R ^ 2 := by
  unfold TranscriptColumn.resetBudget
  have := zeroBank_le R hR T hT
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem finishArena_le (T c : ℕ) (hT : T ≤ R) (hc : c ≤ R) :
    WalkTranscriptColumnArena.finishBudget R (R ^ 2) T c ≤ 70 * R ^ 2 := by
  unfold WalkTranscriptColumnArena.finishBudget
  have := reset_le R hR T c hT hc
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem body_le (N : ℕ) (hN : N ≤ R) : TranscriptColumn.bodyBudget R N ≤ 69 * R ^ 2 := by
  unfold TranscriptColumn.bodyBudget
  have := Nat.mul_le_mul_right (2 * R + 5) hN
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem loop_le (N T : ℕ) (hN : N ≤ R) (hT : T ≤ R) : TranscriptColumn.loopBudget R N T ≤ 75 * R ^ 3 := by
  unfold TranscriptColumn.loopBudget
  have h1 := body_le R hR N hN
  have h2 := Nat.mul_le_mul hT (Nat.add_le_add_right h1 3)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem retreat_le (N : ℕ) (hN : N ≤ R) : TranscriptColumn.retreatBudget R N ≤ 21 * R ^ 2 := by
  unfold TranscriptColumn.retreatBudget
  have := Nat.mul_le_mul_right (2 * R + 5) hN
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem rewind_le (N T : ℕ) (hN : N ≤ R) (hT : T ≤ R) : TranscriptColumn.rewindBudget R N T ≤ 27 * R ^ 3 := by
  unfold TranscriptColumn.rewindBudget
  have h1 := retreat_le R hR N hN
  have h2 := Nat.mul_le_mul hT (Nat.add_le_add_right h1 3)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem column_le (N T c : ℕ) (hN : N ≤ R) (hT : T ≤ R) (hc : c ≤ R) :
    TranscriptColumn.budget R N T c ≤ 169 * R ^ 3 := by
  unfold TranscriptColumn.budget
  have h1 := loop_le R hR N T hN hT
  have h2 := rewind_le R hR N T hN hT
  have h3 := Nat.mul_le_mul_right (2 * R + 5) (Nat.mul_le_mul_left 4 hc)
  have h4 := Nat.mul_le_mul_right (2 * R + 5) (Nat.mul_le_mul_left 2 hT)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

end Col

section Maj
variable (C w : ℕ)

theorem R_pos : 1 ≤ commonReserve C w := by
  unfold commonReserve
  have h1 : 1 ≤ (C + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
  calc 1 = 65536 * 1 * 1 - 65535 := by norm_num
    _ ≤ 65536 * 1 * 1 := Nat.sub_le _ _
    _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

theorem selected_le : SelectedFactorStep.budget C w ≤ 640 * (commonReserve C w) ^ 2 := by
  unfold SelectedFactorStep.budget
  have := R_pos C w
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem selRun_le (N : ℕ) (hN : N ≤ commonReserve C w) :
    BooleanSelectorRun.budget C w N ≤ 646 * (commonReserve C w) ^ 3 := by
  unfold BooleanSelectorRun.budget
  have hR := R_pos C w
  have h1 := selected_le C w
  have h2 := Nat.mul_le_mul hN (Nat.add_le_add_right h1 3)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem selSeek_le (N : ℕ) (hN : N ≤ commonReserve C w) :
    BooleanSelectorSeek.budget N ≤ 23 * (commonReserve C w) ^ 2 := by
  unfold BooleanSelectorSeek.budget
  have hR := R_pos C w
  have h2 := Nat.mul_le_mul hN (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hN) 12)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem selRes_le (N : ℕ) (hN : N ≤ commonReserve C w) :
    BooleanSelectorResident.budget C w N ≤ 685 * (commonReserve C w) ^ 3 := by
  unfold BooleanSelectorResident.budget
  have hR := R_pos C w
  have h1 := selRun_le C w N hN
  have h2 := selSeek_le C w N hN
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem term_le (N : ℕ) (hN : N ≤ commonReserve C w) :
    majorityTermBudget C w N ≤ 772 * (commonReserve C w) ^ 3 := by
  unfold majorityTermBudget
  have hR := R_pos C w
  have h1 := selRes_le C w N hN
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem enum_le (N : ℕ) (hN : N ≤ commonReserve C w) (hP : 2 ^ N ≤ commonReserve C w) :
    MajorityComplete.enumerationBudget C w N ≤ 1558 * (commonReserve C w) ^ 4 := by
  unfold MajorityComplete.enumerationBudget P1Closure.BinaryEnumerator.budget
  have hR := R_pos C w
  have h1 := term_le C w N hN
  have hsub : 2 ^ N - 1 ≤ commonReserve C w := by omega
  have h2 := Nat.mul_le_mul hsub (Nat.add_le_add_right (Nat.add_le_add h1 (Nat.mul_le_mul_left 4 hN)) 6)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem complement_le (N : ℕ) (hN : N ≤ commonReserve C w) :
    ComplementPacketBank.budget C w N ≤ 523 * (commonReserve C w) ^ 3 := by
  unfold ComplementPacketBank.budget
  have hR := R_pos C w
  have h2 := Nat.mul_le_mul hN (le_refl (128 * (commonReserve C w + 1) ^ 2 + 2 * N + 6))
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem fold_le (N : ℕ) (hN : N ≤ commonReserve C w) :
    OrderedPacketFold.budget C w N ≤ 267 * (commonReserve C w) ^ 3 := by
  unfold OrderedPacketFold.budget
  have hR := R_pos C w
  have h2 := Nat.mul_le_mul hN (le_refl (64 * (commonReserve C w + 1) ^ 2 + 2 * N + 6))
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem majority_le (N : ℕ) (hN : N ≤ commonReserve C w) (hP : 2 ^ N ≤ commonReserve C w) :
    MajorityComplete.budget C w N ≤ 2400 * (commonReserve C w) ^ 4 := by
  unfold MajorityComplete.budget
  have hR := R_pos C w
  have h1 := complement_le C w N hN
  have h2 := enum_le C w N hN hP
  have h3 := fold_le C w (2 ^ N) hP
  have h4 : (commonReserve C w) ^ 3 ≤ (commonReserve C w) ^ 4 := Nat.pow_le_pow_right hR (by omega)
  have h5 : (commonReserve C w) ^ 2 ≤ (commonReserve C w) ^ 4 := Nat.pow_le_pow_right hR (by omega)
  have h6 : 1 ≤ (commonReserve C w) ^ 4 := Nat.one_le_pow _ _ hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem consume_le (T : ℕ) (hT : T ≤ commonReserve C w) (hP : 2 ^ T ≤ commonReserve C w) :
    WalkTranscriptColumnArena.consumeBudget C w T ≤ 2428 * (commonReserve C w) ^ 4 := by
  unfold WalkTranscriptColumnArena.consumeBudget WalkTranscriptColumnStore.budget
  have hR := R_pos C w
  have h1 := majority_le C w T hT hP
  have h4 : commonReserve C w ≤ (commonReserve C w) ^ 4 := Nat.le_self_pow (by omega) _
  have h6 : 1 ≤ (commonReserve C w) ^ 4 := Nat.one_le_pow _ _ hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem candidate_le (T c : ℕ) (hT : T ≤ commonReserve C w) (hP : 2 ^ T ≤ commonReserve C w)
    (hc : c ≤ commonReserve C w) :
    WalkTranscriptColumnArena.candidateBudget C w T c ≤ 2500 * (commonReserve C w) ^ 4 := by
  unfold WalkTranscriptColumnArena.candidateBudget
  have hR := R_pos C w
  have h1 := consume_le C w T hT hP
  have h2 := finishArena_le (commonReserve C w) hR T c hT hc
  have h5 : (commonReserve C w) ^ 2 ≤ (commonReserve C w) ^ 4 := Nat.pow_le_pow_right hR (by omega)
  have h6 : 1 ≤ (commonReserve C w) ^ 4 := Nat.one_le_pow _ _ hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem worker_le (N T c : ℕ) (hN : N ≤ commonReserve C w) (hT : T ≤ commonReserve C w)
    (hP : 2 ^ T ≤ commonReserve C w) (hc : c ≤ commonReserve C w) :
    WalkTranscriptColumnArena.workerBudget C w N T c ≤ 2700 * (commonReserve C w) ^ 4 := by
  unfold WalkTranscriptColumnArena.workerBudget
  have hR := R_pos C w
  have h1 := column_le (commonReserve C w) hR N T c hN hT hc
  have h2 := candidate_le C w T c hT hP hc
  have h4 : (commonReserve C w) ^ 3 ≤ (commonReserve C w) ^ 4 := Nat.pow_le_pow_right hR (by omega)
  have h6 : 1 ≤ (commonReserve C w) ^ 4 := Nat.one_le_pow _ _ hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

theorem all_le (population T : ℕ) (hN : population + 1 ≤ commonReserve C w) (hT : T ≤ commonReserve C w)
    (hP : 2 ^ T ≤ commonReserve C w) :
    WalkTranscriptColumn.allBudget C w population T ≤ 5300 * (commonReserve C w) ^ 5 := by
  unfold WalkTranscriptColumn.allBudget WalkTranscriptColumnController.budget
  have hR := R_pos C w
  have h1 := candidate_le C w T 0 hT hP (by omega)
  have h2 := worker_le C w (population + 1) T population hN hT hP (by omega)
  have h3 := Nat.mul_le_mul (show population ≤ commonReserve C w by omega) (Nat.add_le_add_right h2 3)
  have h4 : (commonReserve C w) ^ 4 ≤ (commonReserve C w) ^ 5 := Nat.pow_le_pow_right hR (by omega)
  have h6 : 1 ≤ (commonReserve C w) ^ 5 := Nat.one_le_pow _ _ hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) (R_pos C w)
  nlinarith

end Maj

/-! ## The prefix half -/

section Pre
variable (R : ℕ) (hR : 1 ≤ R)
include hR

theorem template_le (a b : ℕ) (ha : a ≤ R) (hb : b ≤ R) : RepairOrdinary.MatrixUnaryTemplate.budget a b ≤ 44 * R ^ 2 := by
  unfold RepairOrdinary.MatrixUnaryTemplate.budget
  have := Nat.mul_le_mul hb (Nat.add_le_add_right (Nat.mul_le_mul_left 8 ha) 10)
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem scorePower_le (d : ℕ) (hd : d + 3 ≤ R) (hP : 2 ^ d ≤ R) : RepairOrdinary.MatrixScorePower.budget d ≤ 92 * R ^ 2 := by
  unfold RepairOrdinary.MatrixScorePower.budget
  have := template_le R hR (d + 3) (2 ^ d) hd hP
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem power_le (d : ℕ) (hd : d + 3 ≤ R) (hP : 2 ^ d ≤ R) : RepairSource.CloseoutCapacity.Power.budget d ≤ 195 * R ^ 2 := by
  unfold RepairSource.CloseoutCapacity.Power.budget
  have := scorePower_le R hR d hd hP
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem seedPower_le (s : ℕ) (hd : s + 3 ≤ R) (hP : 2 ^ s ≤ R) : Completion.MajorityScalarSeed.powerBudget s ≤ 208 * R ^ 2 := by
  unfold Completion.MajorityScalarSeed.powerBudget CycleTableSeed.budget CycleTableDriver.budget
  have := power_le R hR s hd hP
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem producer_le (n : ℕ) (hd : n + 4 ≤ R) (hP : 2 ^ (n + 1) ≤ R) : Completion.MajorityScalarProducer.budget n ≤ 260 * R ^ 2 := by
  unfold Completion.MajorityScalarProducer.budget Completion.MajorityScalarNumeric.budget
  have := seedPower_le R hR (n + 1) (by omega) hP
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem width_le : MajorityComplete.Width.budget R ≤ 50 * R ^ 2 := by
  unfold MajorityComplete.Width.budget
  simp only [RepairSource.ProjectionNormalization.DimensionPower.cost, RepairOrdinary.WilliamsUnaryProduct.budget,
    pow_zero, pow_one, Nat.one_mul, Nat.mul_one]
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

theorem finishMaj_le : WalkLiteralProducedMajority.finishBudget R ≤ 70 * R ^ 2 := by
  unfold WalkLiteralProducedMajority.finishBudget
  have := width_le R hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows R hR
  nlinarith

end Pre

theorem prefix_le (C w population n : ℕ) (hN : population + 1 ≤ commonReserve C w) (hn : n + 4 ≤ commonReserve C w)
    (hP : 2 ^ (n + 1) ≤ commonReserve C w) :
    WalkLiteralProducedMajority.prefixBudget C w population n ≤
      2 * WalkLiteralProducedMajority.S C w + 500 * (commonReserve C w) ^ 3 := by
  unfold WalkLiteralProducedMajority.prefixBudget WalkLiteralProducedMajority.frontBudget
  have hR := R_pos C w
  have h1 := producer_le (commonReserve C w) hR n hn hP
  have h2 := column_le (commonReserve C w) hR (population + 1) (n + 1) 0 hN (by omega) (by omega)
  have h3 := finishMaj_le (commonReserve C w) hR
  obtain ⟨p2, p3, p4, p5, _, _⟩ := pows (commonReserve C w) hR
  show 2 * WalkLiteralProducedMajority.S C w + 7 + Completion.MajorityScalarProducer.budget n + 1 +
    (2 + TranscriptColumn.budget (commonReserve C w) (population + 1) (n + 1) 0 + 1 +
      (1 + 1 + (WalkLiteralProducedMajority.finishBudget (commonReserve C w) + 2))) ≤ _
  nlinarith

/-! ## The scale facts -/

theorem R_ge (C w : ℕ) : 65536 * 2 ^ (8 * w) ≤ commonReserve C w := by
  unfold commonReserve
  have h1 : 1 ≤ (C + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  calc 65536 * 2 ^ (8 * w) = 65536 * 1 * 2 ^ (8 * w) := by ring
    _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)

theorem pow_le_R (C w : ℕ) : 2 ^ w ≤ commonReserve C w := by
  have h2 : 2 ^ w ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by omega) (by omega)
  have := R_ge C w
  omega

theorem pop_le_R (C w population : ℕ) (hC : population ≤ C) : population + 1 ≤ commonReserve C w := by
  unfold commonReserve
  have h1 : C + 1 ≤ (C + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have h2 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
  calc population + 1 ≤ 1 * (C + 1) * 1 := by omega
    _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) h1) h2

theorem S_le (C w : ℕ) : WalkLiteralProducedMajority.S C w ≤ 2 ^ 102 * (commonReserve C w) ^ 5 := by
  show CyclePaletteReserve.reserve C w ≤ _
  unfold CyclePaletteReserve.reserve commonReserve
  have e1 : (C + 1) ^ 20 * 2 ^ (40 * w) = ((C + 1) ^ 4 * 2 ^ (8 * w)) ^ 5 := by ring
  have e2 : (65536 * (C + 1) ^ 4 * 2 ^ (8 * w)) ^ 5 = 65536 ^ 5 * ((C + 1) ^ 4 * 2 ^ (8 * w)) ^ 5 := by ring
  rw [e2, show 2 ^ 102 * (C + 1) ^ 20 * 2 ^ (40 * w) = 2 ^ 102 * ((C + 1) ^ 20 * 2 ^ (40 * w)) by ring, e1]
  have h : 1 ≤ 65536 ^ 5 := by norm_num
  nlinarith [Nat.zero_le (((C + 1) ^ 4 * 2 ^ (8 * w)) ^ 5)]

theorem reserveTail_le (C w n : ℕ) (hn : n + 1 ≤ commonReserve C w) :
    (n + 1) * (2 ^ 118 * ((C + w + 2) ^ 21 * 2 ^ (40 * w))) ≤ 2 ^ 118 * (commonReserve C w) ^ 27 := by
  have hR := R_pos C w
  have hbase : C + w + 2 ≤ commonReserve C w := by
    unfold commonReserve
    have h1 : C + 1 ≤ (C + 1) ^ 4 := Nat.le_self_pow (by omega) _
    have h2 : w + 1 ≤ 2 ^ (8 * w) := by
      have := Nat.lt_two_pow_self (n := 8 * w)
      omega
    have h3 : 1 ≤ 2 ^ (8 * w) := Nat.one_le_two_pow
    have h4 := Nat.mul_le_mul h1 h2
    have h5 : 1 ≤ C + 1 := by omega
    have h6 := Nat.mul_le_mul (Nat.le_refl ((C + 1) ^ 4)) h3
    calc C + w + 2 ≤ (C + 1) * (w + 1) + (C + 1) * (w + 1) := by nlinarith
      _ ≤ (C + 1) ^ 4 * 2 ^ (8 * w) + (C + 1) ^ 4 * 2 ^ (8 * w) := Nat.add_le_add h4 h4
      _ ≤ 65536 * (C + 1) ^ 4 * 2 ^ (8 * w) := by rw [Nat.mul_assoc 65536]; omega
  have hexp : 2 ^ (40 * w) ≤ (commonReserve C w) ^ 5 := by
    rw [show 40 * w = (8 * w) * 5 by ring, pow_mul]
    exact Nat.pow_le_pow_left ((Nat.pow_le_pow_right (by omega) (by omega)).trans
      (show 2 ^ (8 * w) ≤ commonReserve C w by have := R_ge C w; omega)) 5
  have h21 := Nat.pow_le_pow_left hbase 21
  have hprod := Nat.mul_le_mul h21 hexp
  have hall := Nat.mul_le_mul hn (Nat.mul_le_mul_left (2 ^ 118) hprod)
  calc (n + 1) * (2 ^ 118 * ((C + w + 2) ^ 21 * 2 ^ (40 * w)))
      ≤ commonReserve C w * (2 ^ 118 * ((commonReserve C w) ^ 21 * (commonReserve C w) ^ 5)) := hall
    _ = 2 ^ 118 * (commonReserve C w) ^ 27 := by ring

/-! ## The whole `all_run` budget -/

end NearCubicWires.PacketsCombine.AllRunCost

