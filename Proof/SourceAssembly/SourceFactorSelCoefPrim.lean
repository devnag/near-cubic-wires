import Proof.SourceAssembly.SourceFactorSelCount

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.CoefPrim
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
noncomputable section

theorem pad_nil (R : Nat) : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by
  simp [ZeroPadding.pad]

theorem pad_zeros_le (C k : Nat) (h : k ≤ C) :
    ZeroPadding.pad C (List.replicate k false) = List.replicate C false := by
  rw [Rewind.Workspace.pad_zeros, Nat.max_eq_left h]

/-! ## Framed-field loader (source head advances) -/

theorem load_local (pre bits suffix : List Bool) (T C : Nat) (hC : 2 * bits.length + 1 ≤ C) :
    Step FrameLoad.machine (4 * bits.length + 3) ![pre.length, 0, 0]
      ![pre ++ frame bits ++ suffix, List.replicate T false, List.replicate C false]
      ![pre.length + 2 * bits.length + 1, 0, 0]
      ![pre ++ frame bits ++ suffix, ZeroPadding.pad T (frame bits), List.replicate C false] := by
  obtain ⟨r, hr, hf, hs, _⟩ := FrameLoad.load_run pre bits suffix [] (by simp)
  have base : Step FrameLoad.machine (4 * bits.length + 3) ![pre.length, 0, 0]
      ![pre ++ frame bits ++ suffix, [], []] ![pre.length + 2 * bits.length + 1, 0, 0]
      ![pre ++ frame bits ++ suffix, frame bits, List.replicate (2 * bits.length + 1) false] := by
    refine ⟨r, ?_, ?_, ?_, le_of_eq hs⟩
    · have he : FrameLoad.scan 0 (pre ++ frame bits ++ suffix) pre.length [] [] =
          (⟨FrameLoad.machine.start, ![pre.length, 0, 0], ![pre ++ frame bits ++ suffix, [], []]⟩ :
            Configuration 3 4) := by
        simp only [FrameLoad.scan, StablePartition.Workspace.overlay, List.length_nil, List.drop_nil, List.append_nil,
          List.replicate_zero]
        rfl
      rw [he] at hr
      exact hr
    · rw [hf]
      funext i
      fin_cases i <;> rfl
    · rw [hf]
      funext i
      fin_cases i <;> simp [FrameLoad.reset]
  have hp := base.pad ![0, T, C]
  refine (hp.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · simp
    · exact pad_nil T
    · exact pad_nil C
  · funext i
    fin_cases i
    · simp
    · rfl
    · exact pad_zeros_le C _ hC

theorem rewind_step {t s : Nat} {p : Machine t s} {n : Nat} {tin tout : Fin t → List Bool}
    {hout : Fin t → Nat} (h : Step p n (fun _ => 0) tin hout tout) (C : Nat) (hC : n ≤ C) :
    Step (Rewind.machine p) (2 * n + 2) (fun _ => 0)
      (Fin.addCases tin (fun _ => List.replicate C false)) (fun _ => 0)
      (Fin.addCases tout (fun _ => List.replicate C false)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨r', hr', hf', hs', _⟩ := Rewind.recorded_run p n ⟨p.start, fun _ => 0, tin⟩ r hr 0
    (fun _ => Nat.le_refl _)
  have base : Step (Rewind.machine p) (2 * r.steps + 2) (fun _ => 0) (Fin.addCases tin (fun _ => []))
      (fun _ => 0) (Fin.addCases tout (fun _ => List.replicate r.steps false)) := by
    refine ⟨r', ?_, ?_, ?_, by omega⟩
    · have he : Rewind.recording (⟨p.start, fun _ => 0, tin⟩ : Configuration t s) 0 =
          (⟨(Rewind.machine p).start, fun _ => 0, Fin.addCases tin (fun _ => [])⟩ : Configuration (t + 1) (s + 2)) := by
        simp only [Rewind.recording, Rewind.config]
        congr 1
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      rw [he, Nat.zero_add] at hr'
      exact hr'
    · rw [hf']
      funext i
      simp only [Rewind.finished, Rewind.config]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    · rw [hf']
      simp only [Rewind.finished, Rewind.config, Nat.zero_add]
      rw [ht]
  have hp := (base.pad (Fin.addCases (fun _ => 0) (fun _ => C))).enlarge
    (show 2 * r.steps + 2 ≤ 2 * n + 2 by omega)
  refine (hp.congr_in rfl ?_).congr rfl ?_
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp [pad_nil]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp only [Fin.addCases_right]
      exact pad_zeros_le C _ (by omega)

theorem unary_local (bits : List Bool) (Q S : Nat) : ∃ E' : Fin 7 → List Bool,
    Step RepairSource.RecoveryProjectionDimension.machine (RepairSource.RecoveryProjectionDimension.budget bits)
      (fun _ => 0) ![ZeroPadding.pad Q (frame bits), List.replicate S false, List.replicate S false,
        List.replicate S false, List.replicate S false, List.replicate S false, List.replicate S false]
      (fun _ => 0) E' ∧
    E' 3 = ZeroPadding.pad S (CompareMachine.word (value bits)) ∧
    E' 5 = ZeroPadding.pad S (List.replicate (value bits) true) := by
  obtain ⟨out, hr, h3, h5⟩ := RepairSource.RecoveryProjectionDimension.unary_ready bits
  have hp := (SLoad.MaskFrame.step_of_clockReady hr).pad ![Q, S, S, S, S, S, S]
  refine ⟨_, hp.congr_in rfl ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [RepairSource.RecoveryProjectionDimension.input, pad_nil]
  · show ZeroPadding.pad S (out 3) = ZeroPadding.pad S (CompareMachine.word (value bits))
    rw [h3]
  · show ZeroPadding.pad S (out 5) = ZeroPadding.pad S (List.replicate (value bits) true)
    rw [h5]

theorem count_local (n Q S : Nat) : ∃ E' : Fin 10 → List Bool,
    Step CloseoutRowsCountBinary.machine (CloseoutRowsCountBinary.budget n) (fun _ => 0)
      ![ZeroPadding.pad Q (List.replicate n true), List.replicate S false, List.replicate S false,
        List.replicate S false, List.replicate S false, List.replicate S false, List.replicate S false,
        List.replicate S false, List.replicate S false, List.replicate S false]
      (fun _ => 0) E' ∧
    E' 5 = ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n)) := by
  obtain ⟨out, hr, _, _, h5⟩ := CloseoutRowsCountBinary.count_run n
  have hp := (SLoad.MaskFrame.step_of_clockReady hr).pad ![Q, S, S, S, S, S, S, S, S, S]
  refine ⟨_, hp.congr_in rfl ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [CloseoutRowsCountBinary.input, pad_nil]
  · show ZeroPadding.pad S (out 5) = ZeroPadding.pad S (frame (CloseoutRowsCountBinary.bits n))
    rw [h5]

/-- The normalizer's resize of the count word IS the fixed-width binary word, for every `n`. -/
theorem resize_binary : ∀ (W k n : Nat), n < 2 ^ k → ClockNormalize.resize W (binary k n) = binary W n
  | 0, _, _, _ => rfl
  | W + 1, 0, n, hn => by
    have h0 : n = 0 := by simpa using hn
    subst h0
    show false :: ClockNormalize.resize W [] = (0 % 2 == 1) :: binary W (0 / 2)
    have ih := resize_binary W 0 0 (by decide)
    simp only [binary] at ih
    rw [ih]
    rfl
  | W + 1, k + 1, n, hn => by
    show (n % 2 == 1) :: ClockNormalize.resize W (binary k (n / 2)) = (n % 2 == 1) :: binary W (n / 2)
    rw [resize_binary W k (n / 2) (by rw [pow_succ] at hn; omega)]

theorem resize_bits (W n : Nat) : ClockNormalize.resize W (CloseoutRowsCountBinary.bits n) = binary W n := by
  unfold CloseoutRowsCountBinary.bits
  split
  · rename_i h
    subst h
    exact resize_binary W 0 0 (by decide)
  · exact resize_binary W _ n (Nat.lt_pow_succ_log_self (b := 2) (by decide) n)

theorem norm_local (w : Nat) (bits : List Bool) (Qw Qb R S C : Nat) (hC : 2 * w + 1 ≤ C) :
    Step ClockNormalize.machine (4 * w + 4) (fun _ => 0)
      ![ZeroPadding.pad Qw (List.replicate w true), ZeroPadding.pad Qb (frame bits), List.replicate R false,
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qw (List.replicate w true), ZeroPadding.pad Qb (frame bits),
        ZeroPadding.pad R (frame (ClockNormalize.resize w bits)), ZeroPadding.pad S [decide (bits.length ≤ w)],
        List.replicate C false] := by
  obtain ⟨r, hr, h0, h1, h2, h3, h4, hh, hs⟩ := ClockNormalize.normalize_run w bits
  have base : Step ClockNormalize.machine (4 * w + 4) (fun _ => 0) (ClockNormalize.input w bits) (fun _ => 0)
      r.final.tapes := by
    refine ⟨r, ?_, funext hh, rfl, le_of_eq hs⟩
    change runFrom _ _ (initialConfiguration _ _) = some r at hr
    exact hr
  have hp := base.pad ![Qw, Qb, R, S, C]
  refine (hp.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · rfl
    · rfl
    · exact pad_nil R
    · exact pad_nil S
    · exact pad_nil C
  · funext i
    fin_cases i
    · show ZeroPadding.pad Qw (r.final.tapes 0) = ZeroPadding.pad Qw (List.replicate w true); rw [h0]
    · show ZeroPadding.pad Qb (r.final.tapes 1) = ZeroPadding.pad Qb (frame bits); rw [h1]
    · show ZeroPadding.pad R (r.final.tapes 2) = ZeroPadding.pad R (frame (ClockNormalize.resize w bits)); rw [h2]
    · show ZeroPadding.pad S (r.final.tapes 3) = ZeroPadding.pad S [decide (bits.length ≤ w)]; rw [h3]
    · show ZeroPadding.pad C (r.final.tapes 4) = List.replicate C false; rw [h4]; exact pad_zeros_le C _ hC

/-- The cold initializer then the loop, as one machine. -/
def gcdM := Composition.machine CompetitorGcd.cold CompetitorGcd.machine

def gcdCost (w a b : Nat) : Nat := (12 * w + 15) + 1 + (a + b + 1) * (32 * w + 40)

theorem gcd_local (w a b Qa Qb S : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w) : ∃ E' : Fin 7 → List Bool,
    Step gcdM (gcdCost w a b) (fun _ => 0)
      ![ZeroPadding.pad Qa (frame (binary w a)), ZeroPadding.pad Qb (frame (binary w b)), List.replicate S false,
        List.replicate S false, List.replicate S false, List.replicate S false, List.replicate S false]
      (fun _ => 0) E' ∧
    E' 2 = ZeroPadding.pad S (frame (binary w (Nat.gcd a b))) := by
  obtain ⟨cold, hcold, ct, ch, cs⟩ := CompetitorGcd.cold_ready w a b ha
  have hc : ClockJoin.ReadyRun CompetitorGcd.cold (12 * w + 15)
      (CompetitorGcd.coldInput w a b) (CompetitorGcd.data w a b a false) := ⟨cold, hcold, ct, ch, cs.le⟩
  obtain ⟨t, aa, bb, ht, loop, hloop, lt, lh, ls⟩ := CloseoutWitness.GcdGuard.gcd_ready w a b a ha hb
  have hg : ClockJoin.ReadyRun CompetitorGcd.machine t (CompetitorGcd.data w a b a false)
      (CompetitorGcd.data w aa bb (a.gcd b) true) := ⟨loop, hloop, lt, lh, ls.le⟩
  have hg' := ClockJoin.enlarge CompetitorGcd.machine t ((a + b + 1) * (32 * w + 40)) _ _ hg ht
  have hcg := ClockJoin.join CompetitorGcd.cold CompetitorGcd.machine _ _ _ _ _ hc hg'
  have hp := (SLoad.MaskFrame.step_of_clockReady hcg).pad ![Qa, Qb, S, S, S, S, S]
  refine ⟨_, hp.congr_in rfl ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [CompetitorGcd.coldInput, pad_nil]
  · rfl

theorem div_local (n d Qn Qd S : Nat) (hd : 0 < d) : ∃ E' : Fin 4 → List Bool,
    Step MatrixBucketDivide.machine (8 * n + 6) (fun _ => 0)
      ![ZeroPadding.pad Qn (List.replicate n true), ZeroPadding.pad Qd (UnaryTemplate.tape d),
        List.replicate S false, List.replicate S false] (fun _ => 0) E' ∧
    E' 0 = ZeroPadding.pad Qn (List.replicate n true) ∧ E' 1 = ZeroPadding.pad Qd (UnaryTemplate.tape d) ∧
    E' 2 = ZeroPadding.pad S (List.replicate (n / d) true) := by
  obtain ⟨r, hr, h0, h1, h2, hh, hs⟩ := MatrixBucketDivide.divide_run n d hd
  have hst : Step MatrixBucketDivide.machine (8 * n + 6) (fun _ => 0) (MatrixBucketDivide.resetInput n d)
      (fun _ => 0) r.final.tapes := by
    refine ⟨r, ?_, funext hh, rfl, hs⟩
    change runFrom _ _ (initialConfiguration _ _) = some r at hr
    exact hr
  have hp := hst.pad ![Qn, Qd, S, S]
  refine ⟨_, hp.congr_in rfl ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> rfl
  · show ZeroPadding.pad Qn (r.final.tapes 0) = ZeroPadding.pad Qn (List.replicate n true); rw [h0]
  · show ZeroPadding.pad Qd (r.final.tapes 1) = ZeroPadding.pad Qd (UnaryTemplate.tape d); rw [h1]
  · show ZeroPadding.pad S (r.final.tapes 2) = ZeroPadding.pad S (List.replicate (n / d) true); rw [h2]

theorem cmp_local (a b Qa Qb S C : Nat) (hC : min a b + 2 ≤ C) :
    Step MatrixBucketDimensions.Compare.machine (2 * min a b + 6) (fun _ => 0)
      ![ZeroPadding.pad Qa (UnaryTemplate.tape a), ZeroPadding.pad Qb (List.replicate b true),
        List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Qa (UnaryTemplate.tape a), ZeroPadding.pad Qb (List.replicate b true),
        ZeroPadding.pad S [decide (a ≤ b)], List.replicate C false] := by
  have hp := (SLoad.MaskFrame.step_of_clockReady (RepairSource.CloseoutSchedule.RawCompare.compare_cold a b)).pad
    ![Qa, Qb, S, C]
  refine (hp.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i <;> simp [pad_nil]
  · funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact pad_zeros_le C _ hC

theorem fixed_local (w : List Bool) (S C : Nat) (hC : w.length ≤ C) :
    Step (HierarchyFixedWord.machine w) (2 * w.length + 2) (fun _ => 0)
      ![List.replicate S false, List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad S w, List.replicate C false] := by
  have hp := (Step.of_ready (HierarchyFixedWord.word_ready w)).pad ![S, C]
  refine (hp.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i <;> simp [pad_nil]
  · funext i
    fin_cases i
    · rfl
    · exact pad_zeros_le C _ hC

end
end NearCubicWires.SourceFactorSel.CoefPrim

