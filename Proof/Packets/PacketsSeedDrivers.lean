import Proof.Packets.PacketsSeedDecode
import Proof.Packets.PacketsSetup

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

/-! ## `x ↦ x / 2` -/

namespace Half

/-- States: 0 skip a cell, 1 copy a cell, 2 halt. Tape 0 the input `1^x`, tape 1 the output. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then
      if b 0 then some ⟨1, fun _ => none, fun i => if i.val = 0 then .right else .stay⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then
      if b 0 then some ⟨0, fun i => if i.val = 1 then some true else none, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else none

def cfg (x : ℕ) (q : Fin 3) (i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, o], ![List.replicate x true, List.replicate o true]⟩

theorem step0 (x i o : ℕ) (hi : i < x) : step machine (cfg x 0 i o) = some (cfg x 1 (i + 1) o) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem step1 (x i o : ℕ) (hi : i < x) : step machine (cfg x 1 i o) = some (cfg x 0 (i + 1) (o + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stop0 (x o : ℕ) : step machine (cfg x 0 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stop1 (x o : ℕ) : step machine (cfg x 1 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem pairs (x j i o : ℕ) (h : i + 2 * j ≤ x) :
    Timed machine (2 * j) (cfg x 0 i o) (cfg x 0 (i + 2 * j) (o + j)) := by
  induction j generalizing i o with
  | zero => exact Timed.refl _ _
  | succ j ih =>
    have e : 2 * (j + 1) = 1 + (1 + 2 * j) := by ring
    have h2 := ih (i + 1 + 1) (o + 1) (by omega)
    have e2 : i + 1 + 1 + 2 * j = i + 2 * (j + 1) := by ring
    have e3 : o + 1 + j = o + (j + 1) := by ring
    rw [e2, e3] at h2
    have h := (Timed.single (p := machine) (by rfl) (step0 x i o (by omega))).trans
      ((Timed.single (p := machine) (by rfl) (step1 x (i + 1) o (by omega))).trans h2)
    rw [← e] at h
    exact h

theorem timed (x : ℕ) : Timed machine (x + 1) (cfg x 0 0 0) (cfg x 2 x (x / 2)) := by
  have hp := pairs x (x / 2) 0 0 (by omega)
  rw [Nat.zero_add, Nat.zero_add] at hp
  rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
  · have e1 : 2 * (x / 2) = x := by omega
    rw [e1] at hp
    exact hp.trans (Timed.single (by rfl) (stop0 x (x / 2)))
  · have e1 : 2 * (x / 2) + 1 = x := by omega
    have h1 := Timed.single (p := machine) (by rfl) (step0 x (2 * (x / 2)) (x / 2) (by omega))
    rw [e1] at h1
    have h := (hp.trans h1).trans (Timed.single (by rfl) (stop1 x (x / 2)))
    have e : 2 * (x / 2) + 1 + 1 = x + 1 := by omega
    rw [e] at h
    exact h

theorem run (x : ℕ) :
    Step machine (x + 1) (fun _ => 0) ![List.replicate x true, []] ![x, x / 2]
      ![List.replicate x true, List.replicate (x / 2) true] := by
  obtain ⟨r, hr, hf, _⟩ := (timed x).run (by rfl)
  have hc : cfg x 0 0 0 = (⟨machine.start, fun _ => 0, ![List.replicate x true, []]⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end Half

/-! ## `x ↦ x - 1` -/

namespace Pred

/-- States: 0 skip the first cell, 1 copy, 2 halt. -/
def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q b =>
    if q.val = 0 then
      if b 0 then some ⟨1, fun _ => none, fun i => if i.val = 0 then .right else .stay⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else if q.val = 1 then
      if b 0 then some ⟨1, fun i => if i.val = 1 then some true else none, fun _ => .right⟩
      else some ⟨2, fun _ => none, fun _ => .stay⟩
    else none

def cfg (x : ℕ) (q : Fin 3) (i o : ℕ) : Configuration 2 3 :=
  ⟨q, ![i, o], ![List.replicate x true, List.replicate o true]⟩

theorem step0 (x : ℕ) (hx : 0 < x) : step machine (cfg x 0 0 0) = some (cfg x 1 1 0) := by
  have hr : readTapeBit (List.replicate x true) 0 = true := by simp [readTapeBit, List.getD, hx]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem step1 (x i o : ℕ) (hi : i < x) : step machine (cfg x 1 i o) = some (cfg x 1 (i + 1) (o + 1)) := by
  have hr : readTapeBit (List.replicate x true) i = true := by simp [readTapeBit, List.getD, hi]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stop0 : step machine (cfg 0 0 0 0) = some (cfg 0 2 0 0) := by
  simp only [step, machine, cfg, Configuration.scanned]
  simp [readTapeBit]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem stop1 (x o : ℕ) : step machine (cfg x 1 x o) = some (cfg x 2 x o) := by
  have hr : readTapeBit (List.replicate x true) x = false := by simp [readTapeBit, List.getD]
  simp only [step, machine, cfg, Configuration.scanned]
  simp [hr]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction, HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction]

theorem loop (x m i o : ℕ) (h : i + m = x) : Timed machine (m + 1) (cfg x 1 i o) (cfg x 2 x (o + m)) := by
  induction m generalizing i o with
  | zero =>
    have hi : i = x := by omega
    subst hi
    exact Timed.single (by rfl) (stop1 i o)
  | succ m ih =>
    have h2 := ih (i + 1) (o + 1) (by omega)
    have e3 : o + 1 + m = o + (m + 1) := by ring
    rw [e3] at h2
    have e : m + 1 + 1 = 1 + (m + 1) := by ring
    rw [e]
    exact (Timed.single (by rfl) (step1 x i o (by omega))).trans h2

theorem timed (x : ℕ) : Timed machine (x + 1) (cfg x 0 0 0) (cfg x 2 x (x - 1)) := by
  cases x with
  | zero => exact Timed.single (by rfl) stop0
  | succ k =>
    have h := (Timed.single (p := machine) (by rfl) (step0 (k + 1) (by omega))).trans (loop (k + 1) k 1 0 (by omega))
    have e : 1 + (k + 1) = k + 1 + 1 := by ring
    rw [e, Nat.zero_add] at h
    exact h

theorem run (x : ℕ) :
    Step machine (x + 1) (fun _ => 0) ![List.replicate x true, []] ![x, x - 1]
      ![List.replicate x true, List.replicate (x - 1) true] := by
  obtain ⟨r, hr, hf, _⟩ := (timed x).run (by rfl)
  have hc : cfg x 0 0 0 = (⟨machine.start, fun _ => 0, ![List.replicate x true, []]⟩ : Configuration 2 3) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

end Pred

open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketFamilyParent

/-- A two-tape unary run, head-reset into PG's `UnaryMap` run shape. -/
theorem unaryOfStep {s n x z : ℕ} {M : Machine 2 s} {hout : Fin 2 → ℕ}
    (h : Step M n (fun _ => 0) ![List.replicate x true, []] hout ![List.replicate x true, List.replicate z true]) :
    ∃ (H' : Fin (2 + 1) → ℕ) (A' : Fin (2 + 1) → List Bool),
      Step (MaskedReset.machine M (fun _ => true)) (2 * n + 2) (fun _ => 0) (unIn (2 + 1) x) H' A' ∧
      A' ⟨1, by omega⟩ = List.replicate z true ∧ H' ⟨1, by omega⟩ = 0 := by
  obtain ⟨k, hm⟩ := readyMask h (fun _ => true) (fun _ _ => rfl)
  refine ⟨_, _, hm.congr_in ?_ ?_, rfl, rfl⟩
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]; fin_cases j <;> rfl
    · simp [unIn]

/-- `x ↦ x / 2`. -/
def halfMap : UnaryMap (fun x => x / 2) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine Half.machine (fun _ => true)
  cost := fun x => 2 * (x + 1) + 2
  run := fun x => unaryOfStep (Half.run x)

/-- `x ↦ x - 1`. -/
def predMap : UnaryMap (fun x => x - 1) where
  extra := 1
  states := 3 + 2
  machine := MaskedReset.machine Pred.machine (fun _ => true)
  cost := fun x => 2 * (x + 1) + 2
  run := fun x => unaryOfStep (Pred.run x)

theorem half_cost (x : ℕ) : halfMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * (x + 1) + 2 ≤ _
  rw [pow_one]; omega

theorem pred_cost (x : ℕ) : predMap.cost x ≤ 4 * (x + 3) ^ 1 := by
  change 2 * (x + 1) + 2 ≤ _
  rw [pow_one]; omega

theorem cmp_cost (x : ℕ) : cmpWordMap.cost x ≤ 6 * (x + 3) ^ 1 := by
  change 2 * (x + 2) + 2 ≤ _
  rw [pow_one]; omega

/-! ## The three driver stages -/

section Stages
variable (a : DecompositionAlgorithm)

/-- **The label driver** `1^((t-1)·160)` (entry tape 1 of `seed_ready`), from PG's `walkLength` stage. -/
noncomputable def labelStage (walkS : UnaryStage a (walkLength a)) : UnaryStage a (fun r => (walkLength a r - 1) * 160) :=
  (walkS.thenMapP predMap 4 1 pred_cost).thenMapP (scaleMap 160) (4 * 160 + 12) 2 (scale_cost 160)

/-- **The side counter** `CompareMachine.word (rank·3/2)` (entry tape 2 of `seed_ready`), from PG's `rankStage`. -/
noncomputable def sideWordStage : WordStage a (fun r => CompareMachine.word (rank a r * 3 / 2)) :=
  (((rankStage a).thenMapP (scaleMap 3) (4 * 3 + 12) 2 (scale_cost 3)).thenMapP halfMap 4 1 half_cost).thenWordP
    cmpWordMap 6 1 cmp_cost

noncomputable def stepsWordStage (walkS : UnaryStage a (walkLength a)) :
    WordStage a (fun r => CompareMachine.word (walkLength a r - 1)) :=
  (walkS.thenMapP predMap 4 1 pred_cost).thenWordP cmpWordMap 6 1 cmp_cost

end Stages

/-! ## At the keyed requests: the drivers are `seed_ready`'s, and the seed fits the field -/

open NearCubicWires.PacketsConstruction NearCubicWires.SupplierWalk

theorem side_eq (r : ℕ) : r * 3 / 2 = toeplitzWalkSideBits r := by
  unfold toeplitzWalkSideBits toeplitzSeedBits
  omega

/-- The seed count is `2^(160(t-1) + 2·side)` (`paper.tex:2597`). -/
theorem card_seed {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ) :
    Fintype.card (LiveRows.Seed occ I den) = 2 ^ (labelBits den + 2 * MaskCoord.side occ I) := by
  have hc := card_positiveSample (m := 2 ^ MaskCoord.side occ I) (n := 2 * Nat.clog 2 (den + 1))
  have hv : Fintype.card (MargulisVertex (2 ^ MaskCoord.side occ I)) =
      2 ^ MaskCoord.side occ I * 2 ^ MaskCoord.side occ I := by
    simp [MargulisVertex, ZMod.card]
  rw [hv, card_poweredMargulisLabel] at hc
  change Fintype.card (MargulisWalkSample (2 ^ MaskCoord.side occ I) (2 * Nat.clog 2 (den + 1)).succ) = _
  rw [hc, labelBits_eq]
  have e : (16 : ℕ) ^ 40 = 2 ^ 160 := by norm_num
  rw [e, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

theorem width_of_bound {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den D : ℕ)
    (hD : (Packets.seedList occ I den).length ≤ D) :
    labelBits den + 2 * MaskCoord.side occ I ≤ Nat.log 2 D + 1 := by
  have hl : (Packets.seedList occ I den).length = Fintype.card (LiveRows.Seed occ I den) := by
    simp [Packets.seedList]
  rw [hl, card_seed] at hD
  have := Nat.le_log_of_pow_le (by norm_num) hD
  omega

variable (a : DecompositionAlgorithm)

/-- **The seed fits the key field** (SYM): `seed_ready`'s `hW` at `W = fieldWidth a r`. -/
theorem sym_width (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) :
    labelBits (symmetricListDenominator r0 target) +
        2 * MaskCoord.side (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) ≤
      PacketsConstruction.fieldWidth a (.sym r0 four L target) := by
  unfold PacketsConstruction.fieldWidth
  apply width_of_bound
  simp only [digitBound]
  omega

/-- **The seed fits the key field** (THR). -/
theorem thr_width (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) :
    labelBits (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) +
        2 * MaskCoord.side (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L) ≤
      PacketsConstruction.fieldWidth a (.thr r0 four L target) := by
  unfold PacketsConstruction.fieldWidth
  apply width_of_bound
  simp only [digitBound]
  omega

/-- The label driver's value at a SYM request is `seed_ready`'s `labelBits`. -/
theorem sym_label (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) :
    (walkLength a (.sym r0 four L target) - 1) * 160 = labelBits (symmetricListDenominator r0 target) := by
  unfold walkLength labelBits
  rw [Nat.mul_comm]
  rfl

theorem thr_label (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) :
    (walkLength a (.thr r0 four L target) - 1) * 160 =
      labelBits (CloseoutFinalC10ThresholdRows.listDenominator a r0 target) := by
  unfold walkLength labelBits
  rw [Nat.mul_comm]
  rfl

/-- The side counter's value at a SYM request is `seed_ready`'s `MaskCoord.side`. -/
theorem sym_side (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) :
    rank a (.sym r0 four L target) * 3 / 2 =
      MaskCoord.side (symmetricFourfoldOccurrences r0) (CyclicChoice.live (symmetricFourfoldOccurrences r0) L) := by
  rw [side_eq]
  rfl

theorem thr_side (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (L target : ℕ) :
    rank a (.thr r0 four L target) * 3 / 2 =
      MaskCoord.side (thresholdFourfoldOccurrences r0) (CyclicChoice.live (thresholdFourfoldOccurrences r0) L) := by
  rw [side_eq]
  rfl

/-- The step counter's value at a keyed request is the all-run's `n = t - 1` (`2·clog₂(den+1)`). -/
theorem steps_eq (r : Request) : walkLength a r - 1 = 2 * Nat.clog 2 (Request.denominator a r + 1) := by
  unfold walkLength canonicalWalkLength
  omega

end NearCubicWires.PacketsSeed

