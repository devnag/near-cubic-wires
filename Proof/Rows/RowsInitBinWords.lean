import Proof.Rows.RowsInitThrInitWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.BinWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.BlockPlatform
open RowsInit.VecDock
noncomputable section

/-! ## 1. `natBitLength` as a unary stage -/

theorem bitLen_eq (n : ℕ) : natBitLength n = max 1 (Nat.clog 2 (n + 1)) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hk : Nat.clog 2 (n + 1) = Nat.log 2 n + 1 := by
      apply le_antisymm
      · rw [Nat.clog_le_iff_le_pow (by norm_num)]
        have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
        omega
      · have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := n + 1) (y := Nat.log 2 n)).2 (by
          have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega); omega)
        omega
    rw [hk]; omega

/-- **`natBitLength` of a unary stage's value.** -/
def bitLenS {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v) :
    UnaryStage a (fun r => natBitLength (v r)) :=
  (((s.thenMapP (plusMap 1) (2 * 1 + 4) 1 (plus_cost 1)).thenMapP clogMap 62 1 clog_cost).thenMapP max1Map 4 1
    RowsInit.Count.max1_cost).ofEq (fun r => (bitLen_eq (v r)).symm)

/-! ## 2. `frame (binary W x)` from `1^W`, `1^x` -/

/-- CountBinary's ten tapes: its input `1^x` is local 1, the rest `3..11` (its tape 5, `frame (bits x)`, is local 7). -/
def sC : Fin 10 → Fin 14 := fun i => if i.val = 0 then 1 else ⟨i.val + 2, by omega⟩
/-- ClockNormalize's five tapes: `1^W` (local 0), `frame (bits x)` (local 7), the output (local 2), scratch 12, 13. -/
def sN : Fin 5 → Fin 14 := ![0, 7, 2, 12, 13]

theorem sC_inj : Function.Injective sC := by decide
theorem sN_inj : Function.Injective sN := by decide

def binMachine :=
  Composition.machine (RecoveryFocus.machine sC CloseoutRowsCountBinary.machine)
    (RecoveryFocus.machine sN ClockNormalize.machine)

theorem bin_step (W x : ℕ) : ∃ (A' : Fin 14 → List Bool),
    Step binMachine (CloseoutRowsCountBinary.budget x + 1 + (4 * W + 4)) (fun _ => 0) (unIn2 14 W x) (fun _ => 0) A' ∧
      A' 2 = frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits x)) := by
  obtain ⟨out, ⟨rc, hrc, htc, hhc, hsc⟩, -, -, h5⟩ := CloseoutRowsCountBinary.count_run x
  have hC : Step CloseoutRowsCountBinary.machine (CloseoutRowsCountBinary.budget x) (fun _ => 0)
      (CloseoutRowsCountBinary.input x) (fun _ => 0) out := ⟨rc, hrc, funext hhc, htc, hsc⟩
  have s1 := run_dock hC sC sC_inj (fun _ => 0) (unIn2 14 W x) (fun _ => rfl) (by
    intro j
    fin_cases j <;> rfl)
  set A1 := install sC (unIn2 14 W x) out with hA1
  obtain ⟨rN, hrN, hN0, hN1, hN2, -, -, hNh, hNs⟩ := ClockNormalize.normalize_run W (CloseoutRowsCountBinary.bits x)
  have hN : Step ClockNormalize.machine (4 * W + 4) (fun _ => 0)
      (ClockNormalize.input W (CloseoutRowsCountBinary.bits x)) (fun _ => 0) rN.final.tapes :=
    ⟨rN, hrN, funext hNh, rfl, by omega⟩
  have s2 := run_dock hN sN sN_inj (fun _ => 0) A1 (fun _ => rfl) (by
    intro j
    fin_cases j
    · show A1 0 = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl
    · show A1 7 = _
      rw [show (7 : Fin 14) = sC 5 from rfl, hA1, install_slot _ sC_inj, h5]; rfl
    · show A1 2 = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl
    · show A1 12 = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl
    · show A1 13 = _
      rw [hA1, install_other _ _ _ _ (by decide)]; rfl)
  refine ⟨_, s1.seq s2, ?_⟩
  rw [show (2 : Fin 14) = sN 2 from rfl, install_slot _ sN_inj]
  exact hN2

/-- **`(W, x) ↦ frame (resize W (bits x))`**, one fixed machine. -/
def binMap2 : WordMap2 (fun W x => frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits x))) where
  extra := 11
  states := _
  machine := binMachine
  cost := fun W x => CloseoutRowsCountBinary.budget x + 1 + (4 * W + 4)
  run := by
    intro W x
    obtain ⟨A', h, h2⟩ := bin_step W x
    exact ⟨fun _ => 0, A', h, h2, rfl⟩

theorem bin_cost (W x : ℕ) : binMap2.cost W x ≤ 100 * (W + x + 3) ^ 2 := by
  show 16 * x ^ 2 + 72 * x + 36 + 1 + (4 * W + 4) ≤ _
  nlinarith

theorem bits_length_le (W x : ℕ) (h : x < 2 ^ W) : (CloseoutRowsCountBinary.bits x).length ≤ W := by
  unfold CloseoutRowsCountBinary.bits
  split_ifs with hx
  · simp
  · rw [SignedSortKey.binary_length]
    unfold natBitLength
    have := Nat.log_lt_of_lt_pow (b := 2) (show x ≠ 0 by omega) h
    omega

/-- For `x < 2^W` the word is `frame (binary W x)`. -/
theorem bin_word (W x : ℕ) (h : x < 2 ^ W) :
    frame (ClockNormalize.resize W (CloseoutRowsCountBinary.bits x)) = frame (SignedSortKey.binary W x) := by
  rw [ClockScalarFields.resize_binary W _ (bits_length_le W x h), CloseoutRowsCountBinary.value_bits]

/-- **`frame (binary (vW r) (vx r))`** from two unary stages, when `vx r < 2^(vW r)` for every request. -/
def binWordS {a : DecompositionAlgorithm} {vW vx : Request → ℕ} (sW : UnaryStage a vW) (sx : UnaryStage a vx)
    (h : ∀ r, vx r < 2 ^ vW r) : WordStage a (fun r => frame (SignedSortKey.binary (vW r) (vx r))) :=
  RowsInit.LoopWords.wofEq (sW.pairWP sx binMap2 100 2 bin_cost) (fun r => bin_word (vW r) (vx r) (h r))

/-- `x < 2^(natBitLength x)` (the seed-count word's width). -/
theorem lt_bitLen (x : ℕ) : x < 2 ^ natBitLength x := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) x

end
end RowsInit.BinWords
