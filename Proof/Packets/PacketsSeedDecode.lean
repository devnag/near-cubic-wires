import Proof.Packets.PacketsConeRun
import Proof.Packets.PacketsSeedSplit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction

/-! ## Framed words, cell by cell -/

/-- The frame without its closing `false`. -/
def frameOpen : List Bool → List Bool
  | [] => []
  | b :: bs => true :: b :: frameOpen bs

theorem frame_eq (bs : List Bool) : RepairOrdinary.frame bs = frameOpen bs ++ [false] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [RepairOrdinary.frame, frameOpen, ih]

theorem frameOpen_append (u v : List Bool) : frameOpen (u ++ v) = frameOpen u ++ frameOpen v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [frameOpen, ih]

theorem read_mark : ∀ (bits : List Bool) (i : ℕ), i < bits.length → readTapeBit (RepairOrdinary.frame bits) (2 * i) = true
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: bs, i + 1, h => by
    have ih := read_mark bs i (by simp at h; omega)
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    rw [e]
    simpa [RepairOrdinary.frame, readTapeBit] using ih

theorem read_bit : ∀ (bits : List Bool) (i : ℕ), i < bits.length →
    readTapeBit (RepairOrdinary.frame bits) (2 * i + 1) = bits.getD i false
  | [], _, h => absurd h (by simp)
  | _ :: _, 0, _ => rfl
  | _ :: bs, i + 1, h => by
    have ih := read_bit bs i (by simp at h; omega)
    have e : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by ring
    rw [e]
    simpa [RepairOrdinary.frame, readTapeBit] using ih

theorem take_succ_getD (l : List Bool) (j : ℕ) (h : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem oddCells_frame (bits : List Bool) (n : ℕ) (hn : n ≤ bits.length) :
    oddCells (RepairOrdinary.frame bits) 0 n = bits.take n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [oddCells_succ, ih (by omega), Nat.zero_add, read_bit bits n (by omega), take_succ_getD bits n (by omega)]

theorem pairCells_frame (bits : List Bool) (a n : ℕ) (h : a + n ≤ bits.length) :
    pairCells (RepairOrdinary.frame bits) a n = frameOpen ((bits.drop a).take n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pairCells_succ, ih (by omega), read_mark bits (a + n) (by omega), read_bit bits (a + n) (by omega),
      take_succ_getD (bits.drop a) n (by simp; omega), frameOpen_append]
    simp [frameOpen, List.getD_eq_getElem?_getD]

/-! ## The seed field splits into labels, `y`, `x` -/

theorem binary_zero : ∀ w : ℕ, binary w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by simp [binary, binary_zero w, List.replicate_succ]

/-- **The seed field**, LSB first: the labels, then `y`, then `x`, then zero padding. -/
theorem seed_bits (rank n W : ℕ) (sample : MargulisWalkSample (2 ^ toeplitzWalkSideBits rank) (n + 1))
    (hW : 160 * n + 2 * toeplitzWalkSideBits rank ≤ W) :
    binary W (positiveWalkSampleFinEquiv (2 ^ toeplitzWalkSideBits rank) n sample).val =
      Theorem25Completion.WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++
        (binary (toeplitzWalkSideBits rank) sample.start.2.val ++
          (binary (toeplitzWalkSideBits rank) sample.start.1.val ++
            List.replicate (W - (160 * n + 2 * toeplitzWalkSideBits rank)) false)) := by
  set a := 160 * n + 2 * toeplitzWalkSideBits rank with ha
  set idx := (positiveWalkSampleFinEquiv (2 ^ toeplitzWalkSideBits rank) n sample).val with hidx
  have hlt : idx < 2 ^ a := by
    have hv := Theorem25Completion.WalkSampleWord.value rank sample
    have hl := Theorem25Completion.WalkSampleWord.length rank sample
    have hb := RadixSemantics.value_lt (Theorem25Completion.WalkSampleWord.word rank sample)
    rw [hv, hl] at hb
    exact hb
  have hsplit := Theorem25Completion.WalkSeedBinary.binary_split a (W - a) idx
  rw [show a + (W - a) = W by omega] at hsplit
  rw [hsplit, Nat.div_eq_of_lt hlt, binary_zero, ← Theorem25Completion.WalkSampleWord.binary_eq]
  simp [Theorem25Completion.WalkSampleWord.word, Theorem25Completion.WalkSeedBinary.vertexWord]

section Family
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

/-- The label bits of the seed: `160(t-1)` (`paper.tex:2597`), `t = canonicalWalkLength den`. -/
def labelBits (den : ℕ) : ℕ := 160 * (canonicalWalkLength den - 1)

theorem labelBits_eq : labelBits den = 160 * (2 * Nat.clog 2 (den + 1)) := by
  unfold labelBits canonicalWalkLength
  congr 1

/-- The seed field of a key: `frame (binary W idx)` with `idx` the seed's enumeration index. -/
def seedField (W : ℕ) (sample : LiveRows.Seed occ I den) : List Bool :=
  RepairOrdinary.frame (binary W (canonicalWalkSampleFinEquiv _ _ sample).val)

/-- The split's entry bank at a seed field: the field, the label driver, the side counter. -/
def entry (W : ℕ) (sample : LiveRows.Seed occ I den) : Fin 6 → List Bool :=
  ![seedField occ I den W sample, List.replicate (labelBits den) true,
    CompareMachine.word (MaskCoord.side occ I), [], [], []]

/-- The split's exit bank: inputs kept; labels, `startY`, `startX` on 3, 4, 5. -/
def exit (W : ℕ) (sample : LiveRows.Seed occ I den) : Fin 6 → List Bool :=
  ![seedField occ I den W sample, List.replicate (labelBits den) true,
    CompareMachine.word (MaskCoord.side occ I), MaskCoord.labelsWord occ I den sample,
    MaskCoord.startY occ I den sample, MaskCoord.startX occ I den sample]

/-- The split's fuel. -/
def cost (den : ℕ) : ℕ := 2 * labelBits den + 4 * MaskCoord.side occ I + 3

theorem words (W : ℕ) (sample : LiveRows.Seed occ I den)
    (hW : labelBits den + 2 * MaskCoord.side occ I ≤ W) :
    oddCells (seedField occ I den W sample) 0 (labelBits den) = MaskCoord.labelsWord occ I den sample ∧
    pairCells (seedField occ I den W sample) (labelBits den) (MaskCoord.side occ I) ++ [false] =
      MaskCoord.startY occ I den sample ∧
    pairCells (seedField occ I den W sample) (labelBits den + MaskCoord.side occ I) (MaskCoord.side occ I) ++
      [false] = MaskCoord.startX occ I den sample := by
  have hL := labelBits_eq den
  have hW' : 160 * (2 * Nat.clog 2 (den + 1)) +
      2 * toeplitzWalkSideBits (canonicalGradedRank occ.length (LiveRows.bound occ I)) ≤ W := by
    rw [← hL]; exact hW
  have hb := seed_bits (canonicalGradedRank occ.length (LiveRows.bound occ I)) (2 * Nat.clog 2 (den + 1)) W
    sample hW'
  have hfield : seedField occ I den W sample =
      RepairOrdinary.frame (binary W (positiveWalkSampleFinEquiv (2 ^ toeplitzWalkSideBits
        (canonicalGradedRank occ.length (LiveRows.bound occ I))) (2 * Nat.clog 2 (den + 1)) sample).val) := rfl
  have hlab : (Theorem25Completion.WalkSampleWord.labelsWord (sampleTransitionLabels sample)).length =
      labelBits den := by
    rw [Theorem25Completion.WalkSampleWord.labels_length, hL]
  have hlen : (binary W (positiveWalkSampleFinEquiv (2 ^ toeplitzWalkSideBits
      (canonicalGradedRank occ.length (LiveRows.bound occ I))) (2 * Nat.clog 2 (den + 1)) sample).val).length = W :=
    binary_length _ _
  rw [hfield]
  refine ⟨?_, ?_, ?_⟩
  · rw [oddCells_frame _ _ (by omega), hb, ConeRun.labelsWord_eq]
    rw [List.take_append_of_le_length (by omega), ← hlab, List.take_length]
  · rw [pairCells_frame _ _ _ (by omega), hb, List.drop_append_of_le_length (by omega), ← hlab, List.drop_length,
      List.nil_append, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), ← frame_eq]
    rfl
  · rw [pairCells_frame _ _ _ (by omega), hb, ← List.append_assoc,
      List.drop_append_of_le_length (by simp; omega)]
    rw [show labelBits den + MaskCoord.side occ I =
        (Theorem25Completion.WalkSampleWord.labelsWord (sampleTransitionLabels sample) ++
          binary (toeplitzWalkSideBits (canonicalGradedRank occ.length (LiveRows.bound occ I)))
            sample.start.2.val).length by simp [hlab]]
    rw [List.drop_length, List.nil_append, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp), ← frame_eq]
    rfl

theorem seed_decode (W : ℕ) (sample : LiveRows.Seed occ I den)
    (hW : labelBits den + 2 * MaskCoord.side occ I ≤ W) :
    Step machine (cost occ I den) (fun _ => 0) (entry occ I den W sample)
      ![2 * (labelBits den + MaskCoord.side occ I + MaskCoord.side occ I), labelBits den, 0, labelBits den,
        2 * MaskCoord.side occ I, 2 * MaskCoord.side occ I]
      (exit occ I den W sample) := by
  obtain ⟨h1, h2, h3⟩ := words occ I den W sample hW
  have hs := split_run (seedField occ I den W sample) (labelBits den) (MaskCoord.side occ I)
  unfold cost entry exit
  rw [← h1, ← h2, ← h3]
  exact hs

end Family

theorem readyMask {t s : ℕ} {p : Machine t s} {n : ℕ} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (selected : Fin t → Bool)
    (hstart : ∀ i, selected i = true → hin i = 0) :
    ∃ k, Step (MaskedReset.machine p selected) (2 * n + 2)
      (Fin.addCases hin (fun _ : Fin 1 => 0))
      (Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool)))
      (Fin.addCases (fun i => if selected i then 0 else hout i) (fun _ : Fin 1 => 0))
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate k false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hhead : ∀ i, selected i = true → r.final.heads i ≤ r.steps := by
    intro i hi
    have h1 := SelectiveReset.prefix_head (prefix_of_run p n _ r hr).1 i
    have h0 : (⟨p.start, hin, tin⟩ : Configuration t s).heads i = 0 := hstart i hi
    omega
  obtain ⟨result, hres, hfinal, hsteps, _⟩ := MaskedReset.reset_run p selected n _ r hr hhead
  have hentry : Rewind.recording (⟨p.start, hin, tin⟩ : Configuration t s) 0 =
      (⟨(MaskedReset.machine p selected).start, Fin.addCases hin (fun _ : Fin 1 => 0),
        Fin.addCases tin (fun _ : Fin 1 => ([] : List Bool))⟩ : Configuration (t+1) (s+2)) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
      · simp only [Rewind.recording, Rewind.config, Fin.addCases_left]
      · have hj : j = 0 := Fin.eq_zero j
        subst hj
        simp only [Rewind.recording, Rewind.config, Fin.addCases_right, List.replicate_zero]
  rw [hentry] at hres
  have hfuel : 2 * r.steps + 2 ≤ 2 * n + 2 := by omega
  have hmore := runFrom_moreFuel (MaskedReset.machine p selected) (2 * r.steps + 2)
    (2 * n + 2 - (2 * r.steps + 2)) _ result hres
  rw [Nat.add_sub_of_le hfuel] at hmore
  refine ⟨r.steps, result, hmore, ?_, ?_, by omega⟩
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, hh]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]
  · rw [hfinal]
    funext i
    refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_left, ht]
    · have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp only [SelectiveReset.finished, Rewind.config, Fin.addCases_right]

/-- The seed decode's fixed machine with its head reset: seven tapes (the six of `PacketsSeedSplit.machine`,
then the reset log). -/
noncomputable def readyMachine : Machine 7 9 := MaskedReset.machine machine (fun _ => true)

section Ready
variable {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (den : ℕ)

/-- The ready entry: the split's entry, then the empty log. -/
def readyEntry (W : ℕ) (sample : LiveRows.Seed occ I den) : Fin 7 → List Bool :=
  Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool) (entry occ I den W sample) (fun _ => [])

/-- The ready exit: the split's exit, then the log `0^k`. -/
def readyExit (W : ℕ) (sample : LiveRows.Seed occ I den) (k : ℕ) : Fin 7 → List Bool :=
  Fin.addCases (m := 6) (n := 1) (motive := fun _ => List Bool) (exit occ I den W sample)
    (fun _ => List.replicate k false)

theorem seed_ready (W : ℕ) (sample : LiveRows.Seed occ I den)
    (hW : labelBits den + 2 * MaskCoord.side occ I ≤ W) :
    ∃ k, Step readyMachine (2 * cost occ I den + 2) (fun _ => 0) (readyEntry occ I den W sample) (fun _ => 0)
      (readyExit occ I den W sample k) := by
  obtain ⟨k, hk⟩ := readyMask (seed_decode occ I den W sample hW) (fun _ => true) (fun _ _ => rfl)
  refine ⟨k, Step.congr (Step.congr_in hk ?_ rfl) ?_ rfl⟩
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

end Ready

end NearCubicWires.PacketsSeed
