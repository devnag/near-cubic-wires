import Proof.Packets.PacketsSetup
import Proof.Packets.PacketsWalk
import Proof.Rows.RowsInitLoopFan

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RowsInit.LoopWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## 1. `C·(x+1)^D` as a unary map -/

theorem tapesEq (D : ℕ) : UnaryCalc.tapes D = 2 + (12 + 2*D) := by
  simp only [UnaryCalc.tapes, RepairSource.ProjectionNormalization.DimensionPolynomial.tapes]
  omega

def castT (D : ℕ) : Fin (UnaryCalc.tapes D) → Fin (2 + (12 + 2*D)) := Fin.cast (tapesEq D)

theorem castT_inj (D : ℕ) : Function.Injective (castT D) := Fin.cast_injective _

theorem castT_val (D : ℕ) (j : Fin (UnaryCalc.tapes D)) : (castT D j).val = j.val := rfl

theorem castT_out_ne (D : ℕ) : (castT D (UnaryCalc.outputTape D)).val ≠ 0 := by
  intro h
  rw [castT_val] at h
  exact UnaryCalc.output_ne_input D (Fin.ext (by rw [h]; rfl))

def polyMap (D C : ℕ) : UnaryMap (fun x => UnaryCalc.value D C x) :=
  UnaryMap.ofSwap (e := 12 + 2*D) (RecoveryFocus.machine (castT D) (PCPSerializerCapacity.Power.machine D C))
    (castT D (UnaryCalc.outputTape D)) (castT_out_ne D) (PCPSerializerCapacity.Power.budget D C) (fun x => by
      obtain ⟨out, h, _, h1⟩ := UnaryCalc.poly_step D C x
      have d := h.dock (castT D) (castT_inj D) (fun _ => 0) (unIn (2 + (12 + 2*D)) x) (fun _ => rfl) (by
        intro j
        simp only [unIn, RepairSource.ProjectionNormalization.DimensionPolynomial.input, castT_val]
        by_cases hj : j.val = 0 <;> simp [hj])
      refine ⟨_, d.congr (ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)) rfl, ?_⟩
      rw [install_slot _ (castT_inj D)]
      exact h1)

theorem poly_cost (D C x : ℕ) : (polyMap D C).cost x ≤ UnaryCalc.polyCoefficient D C * (x + 3) ^ (D+1) := by
  have h := UnaryCalc.poly_cost_polyBounded D C x
  unfold ValidatorPolynomialDomination.PolyBounded at h
  have hm : (x + 1) ^ (D+1) ≤ (x + 3) ^ (D+1) := Nat.pow_le_pow_left (by omega) _
  exact le_trans h (Nat.mul_le_mul_left _ hm)

/-! ## 2. Constant stages, word-stage transport -/

/-- The machine that halts at once (2 tapes). -/
def stop2 : Machine 2 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

/-- **The value `0`.** -/
def zeroStage (a : DecompositionAlgorithm) : UnaryStage a (fun _ => 0) where
  extra := 0
  states := 1
  machine := stop2
  cost := fun _ => 0
  coefficient := 0
  degree := 0
  cost_le := fun _ => Nat.zero_le _
  run := by
    intro r
    exact ⟨fun _ => 0, inBank (2 + 0) (Request.input a r),
      ⟨_, runFrom_zero_of_halted stop2 _ rfl, rfl, rfl, le_refl 0⟩, rfl, rfl, rfl, rfl⟩

/-- **A constant `c`.** -/
def constStage (a : DecompositionAlgorithm) (c : ℕ) : UnaryStage a (fun _ => c) :=
  ((zeroStage a).thenMapP (plusMap c) (2 * c + 4) 1 (plus_cost c)).ofEq (fun _ => by simp)

/-- Transport a word stage along a pointwise equality of words. -/
def wofEq {a : DecompositionAlgorithm} {w w' : Request → List Bool} (s : WordStage a w)
    (h : ∀ r, w r = w' r) : WordStage a w' where
  extra := s.extra
  states := s.states
  machine := s.machine
  cost := s.cost
  coefficient := s.coefficient
  degree := s.degree
  cost_le := s.cost_le
  run := fun r => by
    obtain ⟨H', A', hs, h0, hh0, h1, hh1⟩ := s.run r
    exact ⟨H', A', hs, h0, hh0, by rw [h1, h r], hh1⟩

/-- Splitter slots for a FRAMED field: input `0 ↦ 0`, field `j` (splitter tape `j+3`) `↦ 1`, the rest `↦ 2..12`. -/
def fSlots (j : Fin 5) (i : Fin 13) : Fin (2 + 11) :=
  if i.val = 0 then ⟨0, by omega⟩ else if i.val = j.val + 3 then ⟨1, by omega⟩
  else if h2 : i.val < j.val + 3 then ⟨i.val + 1, by have := j.isLt; omega⟩ else ⟨i.val, by have := i.isLt; omega⟩

theorem fSlots_val (j : Fin 5) (i : Fin 13) : (fSlots j i).val =
    if i.val = 0 then 0 else if i.val = j.val + 3 then 1 else if i.val < j.val + 3 then i.val + 1 else i.val := by
  unfold fSlots
  split_ifs <;> rfl

theorem fSlots_inj (j : Fin 5) : Function.Injective (fSlots j) := by
  fin_cases j <;> decide

theorem fSlots_zero (j : Fin 5) (i : Fin 13) : (fSlots j i).val = 0 ↔ i.val = 0 := by
  rw [fSlots_val]
  by_cases h0 : i.val = 0
  · simp [h0]
  · rw [if_neg h0]
    constructor
    · intro h
      split_ifs at h <;> omega
    · intro h
      exact absurd h h0

theorem fSlots_field (j : Fin 5) : fSlots j ⟨j.val + 3, by omega⟩ = ⟨1, by omega⟩ := by
  unfold fSlots
  rw [if_neg (by simp), if_pos rfl]

theorem fSlots_in (j : Fin 5) : fSlots j ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  unfold fSlots
  rw [if_pos rfl]

theorem bank_field (ws : Fin 5 → List Bool) (j : Fin 5) :
    PCJ45bee56da9f34d5a_RequestFields.bank ws 5 ⟨j.val + 3, by omega⟩ = frame (ws j) := by
  fin_cases j <;> rfl

theorem heads_field (ws : Fin 5 → List Bool) (j : Fin 5) :
    PCJ45bee56da9f34d5a_RequestFields.heads ws 5 ⟨j.val + 3, by omega⟩ = 0 := by
  unfold PCJ45bee56da9f34d5a_RequestFields.heads
  rw [if_neg (by intro h; have := congrArg Fin.val h; simp at this)]

theorem request_in (a : DecompositionAlgorithm) (r : Request) (n : ℕ) (sl : Fin 13 → Fin n)
    (hz : ∀ i, (sl i).val = 0 ↔ i.val = 0) (i : Fin 13) :
    inBank n (Request.input a r) (sl i) = (fun i : Fin 13 => if i = 0 then frame (r.input a) else []) i := by
  dsimp only
  unfold inBank
  by_cases hi : i.val = 0
  · have h0 : i = 0 := Fin.ext hi
    rw [if_pos ((hz i).mpr hi), if_pos h0]
  · have h0 : i ≠ 0 := fun h => hi (by rw [h]; rfl)
    rw [if_neg (fun h => hi ((hz i).mp h)), if_neg h0]

/-- **A framed request field as a word stage** (`frame (fields a r j)` on tape 1). -/
def framedField (a : DecompositionAlgorithm) (j : Fin 5) : WordStage a (fun r => frame (fields a r j)) where
  extra := 11
  states := _
  machine := RecoveryFocus.machine (fSlots j) PCJ45bee56da9f34d5a_RequestFields.machine
  cost := fun r => 6 * (r.input a).length + 17
  coefficient := 23
  degree := 1
  cost_le := by
    intro r
    have h := input_le_small a r
    rw [pow_one]
    omega
  run := by
    intro r
    have d := (PCJ45bee56da9f34d5a_RequestFields.request_run a r).dock (fSlots j) (fSlots_inj j) (fun _ => 0)
      (inBank (2 + 11) (Request.input a r)) (fun _ => rfl) (request_in a r _ (fSlots j) (fSlots_zero j))
    refine ⟨_, _, d, ?_, ?_, ?_, ?_⟩
    · rw [← fSlots_in j, install_slot _ (fSlots_inj j)]
      change frame (PCJ45bee56da9f34d5a_RequestFields.word (PCJ45bee56da9f34d5a_RequestFields.values a r)) = _
      rw [PCJ45bee56da9f34d5a_RequestFields.word_values]
    · rw [← fSlots_in j, dockH_slot _ (fSlots_inj j)]
      rfl
    · rw [← fSlots_field j, install_slot _ (fSlots_inj j), bank_field]
    · rw [← fSlots_field j, dockH_slot _ (fSlots_inj j), heads_field]

/-- Splitter slots for an UNWRAPPED field: input `0 ↦ 0`, field `j ↦ 2`, the rest `↦ 3..13`; tape 1 the output,
tape 14 the unwrap log. -/
def uSlots (j : Fin 5) (i : Fin 13) : Fin (2 + 13) :=
  if i.val = 0 then ⟨0, by omega⟩ else if i.val = j.val + 3 then ⟨2, by omega⟩
  else if h2 : i.val < j.val + 3 then ⟨i.val + 2, by have := j.isLt; omega⟩ else ⟨i.val + 1, by have := i.isLt; omega⟩

theorem uSlots_val (j : Fin 5) (i : Fin 13) : (uSlots j i).val =
    if i.val = 0 then 0 else if i.val = j.val + 3 then 2 else if i.val < j.val + 3 then i.val + 2 else i.val + 1 := by
  unfold uSlots
  split_ifs <;> rfl

theorem uSlots_inj (j : Fin 5) : Function.Injective (uSlots j) := by
  fin_cases j <;> decide

theorem uSlots_zero (j : Fin 5) (i : Fin 13) : (uSlots j i).val = 0 ↔ i.val = 0 := by
  rw [uSlots_val]
  by_cases h0 : i.val = 0
  · simp [h0]
  · rw [if_neg h0]
    constructor
    · intro h
      split_ifs at h <;> omega
    · intro h
      exact absurd h h0

theorem uSlots_field (j : Fin 5) : uSlots j ⟨j.val + 3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold uSlots
  rw [if_neg (by simp), if_pos rfl]

theorem uSlots_in (j : Fin 5) : uSlots j ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  unfold uSlots
  rw [if_pos rfl]

theorem uSlots_ne1 (j : Fin 5) (i : Fin 13) : uSlots j i ≠ ⟨1, by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  rw [uSlots_val] at hv
  have := i.isLt
  have := j.isLt
  split_ifs at hv <;> simp at hv <;> omega

theorem uSlots_ne14 (j : Fin 5) (i : Fin 13) : uSlots j i ≠ ⟨14, by omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  rw [uSlots_val] at hv
  have := i.isLt
  have := j.isLt
  split_ifs at hv <;> simp at hv <;> omega

/-- The unwrap's slots: framed field, output, log. -/
def wSlots : Fin 3 → Fin (2 + 13) := ![⟨2, by omega⟩, ⟨1, by omega⟩, ⟨14, by omega⟩]

theorem wSlots_inj : Function.Injective wSlots := by decide

/-- **An unwrapped request field as a word stage** (`fields a r j` on tape 1). -/
def rawField (a : DecompositionAlgorithm) (j : Fin 5) : WordStage a (fun r => fields a r j) where
  extra := 13
  states := _
  machine := Composition.machine (RecoveryFocus.machine (uSlots j) PCJ45bee56da9f34d5a_RequestFields.machine)
    (RecoveryFocus.machine wSlots Streaming.machine)
  cost := fun r => 6 * (r.input a).length + 17 + 1 + (4 * (fields a r j).length + 2)
  coefficient := 30
  degree := 1
  cost_le := by
    intro r
    have h := input_le_small a r
    have hf := field_le_input a r j
    rw [frame_length] at hf
    rw [pow_one]
    omega
  run := by
    intro r
    have d := (PCJ45bee56da9f34d5a_RequestFields.request_run a r).dock (uSlots j) (uSlots_inj j) (fun _ => 0)
      (inBank (2 + 13) (Request.input a r)) (fun _ => rfl) (request_in a r _ (uSlots j) (uSlots_zero j))
    obtain ⟨rc, hr, ht, hh, _⟩ := UInputFields.unwrap_ready (fields a r j)
    have w0 := Step.of_run hr (funext hh) ht
    set H1 := dockH (uSlots j) (fun _ => 0)
      (PCJ45bee56da9f34d5a_RequestFields.heads (PCJ45bee56da9f34d5a_RequestFields.values a r) 5) with hH1
    set A1 := install (uSlots j) (inBank (2 + 13) (Request.input a r))
      (PCJ45bee56da9f34d5a_RequestFields.bank (PCJ45bee56da9f34d5a_RequestFields.values a r) 5) with hA1
    have h1f : H1 ⟨2, by omega⟩ = 0 := by
      rw [hH1, ← uSlots_field j, dockH_slot _ (uSlots_inj j), heads_field]
    have a1f : A1 ⟨2, by omega⟩ = frame (fields a r j) := by
      rw [hA1, ← uSlots_field j, install_slot _ (uSlots_inj j), bank_field]
    have h1o : H1 ⟨1, by omega⟩ = 0 := by
      rw [hH1, dockH_other _ _ _ _ (fun i => uSlots_ne1 j i)]
    have a1o : A1 ⟨1, by omega⟩ = [] := by
      rw [hA1, install_other _ _ _ _ (fun i => uSlots_ne1 j i)]
      rfl
    have h1l : H1 ⟨14, by omega⟩ = 0 := by
      rw [hH1, dockH_other _ _ _ _ (fun i => uSlots_ne14 j i)]
    have a1l : A1 ⟨14, by omega⟩ = [] := by
      rw [hA1, install_other _ _ _ _ (fun i => uSlots_ne14 j i)]
      rfl
    have w1 := w0.dock wSlots wSlots_inj H1 A1
      (by intro k; fin_cases k
          · exact h1f
          · exact h1o
          · exact h1l)
      (by intro k; fin_cases k
          · exact a1f
          · exact a1o
          · exact a1l)
    refine ⟨_, _, d.seq w1, ?_, ?_, ?_, ?_⟩
    · rw [install_other _ _ _ _ (by intro k; fin_cases k <;> decide), hA1, ← uSlots_in j,
        install_slot _ (uSlots_inj j)]
      change frame (PCJ45bee56da9f34d5a_RequestFields.word (PCJ45bee56da9f34d5a_RequestFields.values a r)) = _
      rw [PCJ45bee56da9f34d5a_RequestFields.word_values]
    · rw [dockH_other _ _ _ _ (by intro k; fin_cases k <;> decide), hH1, ← uSlots_in j,
        dockH_slot _ (uSlots_inj j)]
      rfl
    · rw [show (⟨1, by omega⟩ : Fin (2 + 13)) = wSlots 1 from rfl, install_slot _ wSlots_inj]
      rfl
    · rw [show (⟨1, by omega⟩ : Fin (2 + 13)) = wSlots 1 from rfl, dockH_slot _ wSlots_inj]

/-! ## 4. The 24 words -/

section Words
variable (a : DecompositionAlgorithm)
open RowsConstruction RowsConstruction.BaseLayout

/-- `T+1`, `T = |input|`. -/
def t1S : UnaryStage a (fun r => (r.input a).length + 1) :=
  (inputLenStage a).thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)

/-- `k·(T+1) + c`. -/
def affS (k c : ℕ) : UnaryStage a (fun r => UnaryCalc.value 1 k (r.input a).length + c) :=
  ((inputLenStage a).thenMapP (polyMap 1 k) (UnaryCalc.polyCoefficient 1 k) (1+1) (poly_cost 1 k)).thenMapP
    (plusMap c) (2 * c + 4) 1 (plus_cost c)

/-- `2T+q+1`. -/
def mS : UnaryStage a (fun r => (r.input a).length + (r.input a).length + r.q + 1) :=
  (((inputLenStage a).pairP (inputLenStage a) addMap2 6 1 add_cost).pairP (qStage a) addMap2 6 1 add_cost).thenMapP
    (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)

/-- `q + (12(T+1)+7)`. -/
def qwS : UnaryStage a (fun r => r.q + (UnaryCalc.value 1 12 (r.input a).length + 7)) :=
  (qStage a).pairP (affS a 12 7) addMap2 6 1 add_cost

theorem val1 (k T : ℕ) : UnaryCalc.value 1 k T = k * (T + 1) := by
  simp [UnaryCalc.value]

theorem resize_nil (n : ℕ) : ClockNormalize.resize n [] = SignedSortKey.binary n 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ClockNormalize.resize, SignedSortKey.binary, ih]

theorem resize_one (n : ℕ) : ClockNormalize.resize (n + 1) (List.replicate 1 true) = SignedSortKey.binary (n + 1) 1 := by
  simp [ClockNormalize.resize, SignedSortKey.binary, resize_nil]

def w0 : WordStage a (fun r => List.replicate ((r.input a).length + 1) true) := (t1S a).toWord
def w1 : WordStage a (fun r => frame (SignedSortKey.binary ((r.input a).length + 1) 0)) :=
  (t1S a).thenWordP zeroWordMap 8 1 zero_cost
def w2 : WordStage a (fun r => List.replicate (P1Closure.HardwireBudget.C ((r.input a).length + 1)) true) :=
  wofEq (affS a 8 12).toWord (fun r => by rw [val1]; simp [P1Closure.HardwireBudget.C])
def w3 : WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word r.q) :=
  (qStage a).thenWordP cmpWordMap 6 1 cmp_cost
def w4 : WordStage a (fun _ => RepairSource.VerifierDecoding.CompareMachine.word 0) :=
  (zeroStage a).thenWordP cmpWordMap 6 1 cmp_cost
def w5 : WordStage a (fun r => List.replicate
    (PCJ45bee56da9f34d5a_UniformMinimumBounds.R (r.input a).length r.q ((r.input a).length + 1)) true) :=
  wofEq ((mS a).thenMapP (polyMap 2 1024) (UnaryCalc.polyCoefficient 2 1024) (2+1) (poly_cost 2 1024)).toWord
    (fun r => by simp only [UnaryCalc.value, PCJ45bee56da9f34d5a_UniformMinimumBounds.R]; ring_nf)
def w6 : WordStage a (fun r => List.replicate
    (PCJ45bee56da9f34d5a_UniformMinimumBounds.U (r.input a).length r.q ((r.input a).length + 1)) true) :=
  wofEq ((mS a).thenMapP (polyMap 2 2048) (UnaryCalc.polyCoefficient 2 2048) (2+1) (poly_cost 2 2048)).toWord
    (fun r => by
      simp only [UnaryCalc.value, PCJ45bee56da9f34d5a_UniformMinimumBounds.U,
        PCJ45bee56da9f34d5a_FullGateCapacity.capacity]; ring_nf)
def w7 : WordStage a (fun r => CyclicChoice.mask (r.family a).occurrences r.liveScale) :=
  wofEq (rawField a 2) (fun _ => rfl)
def w8 : WordStage a (fun r => List.replicate
    (PCJ45bee56da9f34d5a_UniformMinimumBounds.H (r.input a).length r.q ((r.input a).length + 1)) true) :=
  wofEq ((mS a).thenMapP (polyMap 1 64) (UnaryCalc.polyCoefficient 1 64) (1+1) (poly_cost 1 64)).toWord
    (fun r => by simp only [UnaryCalc.value, PCJ45bee56da9f34d5a_UniformMinimumBounds.H]; ring_nf)
def w9 : WordStage a (fun r => r.nativeWord) := wofEq (rawField a 0) (fun _ => rfl)
def w10 : WordStage a (fun r => List.replicate (2 * (12 * (r.input a).length + 19) + 1) true) :=
  wofEq (affS a 24 15).toWord (fun r => by rw [val1]; ring_nf)
def w11 : WordStage a (fun r => frame (SignedSortKey.binary (12 * (r.input a).length + 19) 0)) :=
  wofEq ((affS a 12 7).thenWordP zeroWordMap 8 1 zero_cost) (fun r => by rw [val1]; ring_nf)
def w12 : WordStage a (fun r => RepairSource.VerifierDecoding.CompareMachine.word
    (2 * (2 * (12 * (r.input a).length + 19) + 1))) :=
  wofEq ((affS a 48 30).thenWordP cmpWordMap 6 1 cmp_cost) (fun r => by rw [val1]; ring_nf)
def w13 : WordStage a (fun r => frame (SignedSortKey.binary (12 * (r.input a).length + 19) 1)) :=
  wofEq ((affS a 12 7).pairWP (constStage a 1) flagWordMap2 16 1 flag_cost) (fun r => by
    have e : UnaryCalc.value 1 12 (r.input a).length + 7 = (12 * (r.input a).length + 18) + 1 := by rw [val1]; ring
    have e2 : 12 * (r.input a).length + 19 = (12 * (r.input a).length + 18) + 1 := by ring
    rw [e, e2, resize_one])
def w14 : WordStage a (fun r => List.replicate (ThrBounds.UOf thrCU thrDU r.q (r.input a).length) true) :=
  wofEq ((qwS a).thenMapP (polyMap thrDU thrCU) (UnaryCalc.polyCoefficient thrDU thrCU) (thrDU+1)
    (poly_cost thrDU thrCU)).toWord (fun r => by
      rw [val1, RowsInit.ThrParams.UOf_value]
      congr 2)
def w15 : WordStage a (fun r => List.replicate (ThrBounds.FOf thrCF thrDF r.q (r.input a).length) true) :=
  wofEq ((qwS a).thenMapP (polyMap thrDF thrCF) (UnaryCalc.polyCoefficient thrDF thrCF) (thrDF+1)
    (poly_cost thrDF thrCF)).toWord (fun r => by
      rw [val1, RowsInit.ThrParams.FOf_value]
      congr 2)
def w16 : WordStage a (fun _ => RepairSource.VerifierDecoding.CompareMachine.word 1) :=
  (constStage a 1).thenWordP cmpWordMap 6 1 cmp_cost
def w17 : WordStage a (fun _ => RepairSource.VerifierDecoding.CompareMachine.word 2) :=
  (constStage a 2).thenWordP cmpWordMap 6 1 cmp_cost
def w18 : WordStage a (fun _ => RepairSource.VerifierDecoding.CompareMachine.word 3) :=
  (constStage a 3).thenWordP cmpWordMap 6 1 cmp_cost
def w19 : WordStage a (fun _ => UnaryTemplate.tape 0) := (zeroStage a).tplP
def w20 : WordStage a (fun r => UnaryTemplate.tape (RowsInit.LoopFan.circOf r)) :=
  wofEq (circStage a).tplP (fun r => by cases r <;> rfl)
def w21 : WordStage a (fun r => List.replicate (r.input a).length true) := (inputLenStage a).toWord
def w22 : WordStage a (fun r => frame (r.topWord a)) := wofEq (framedField a 4) (fun _ => rfl)
def w23 : WordStage a (fun r => List.replicate (thrRes r.q (r.input a).length) true) :=
  ((qStage a).pairP (inputLenStage a) addMap2 6 1 add_cost).thenMapP (polyMap thrRd (thrRc+1))
    (UnaryCalc.polyCoefficient thrRd (thrRc+1)) (thrRd+1) (poly_cost thrRd (thrRc+1)) |>.toWord

end Words

/-! ## 5. The vector stage: all 24 words in one fixed machine -/

/-- **The loop block's request-level words**: the 23 fanout sources on tapes 1..23, `1^R` on tape 24. -/
def loopVec (a : DecompositionAlgorithm) :=
  ((((((((((((((((((((((((VecStage.nil a (fun _ _ => [])).snoc (w0 a)).snoc (w1 a)).snoc (w2 a)).snoc (w3 a)).snoc (w4 a)).snoc (w5 a)).snoc (w6 a)).snoc (w7 a)).snoc (w8 a)).snoc (w9 a)).snoc (w10 a)).snoc (w11 a)).snoc (w12 a)).snoc (w13 a)).snoc (w14 a)).snoc (w15 a)).snoc (w16 a)).snoc (w17 a)).snoc (w18 a)).snoc (w19 a)).snoc (w20 a)).snoc (w21 a)).snoc (w22 a)).snoc (w23 a)

theorem loop_cost_le (a : DecompositionAlgorithm) (r : Request) :
    (loopVec a).cost r ≤ (loopVec a).coefficient * (r.smallSize a) ^ (loopVec a).degree :=
  (loopVec a).cost_le r

end
end RowsInit.LoopWords
