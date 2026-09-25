import Proof.Rows.RowsInitLoopFan

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSectionVars false

namespace RowsInit.SymLoopFan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open RowsConstruction RowsConstruction.BaseLayout
noncomputable section

/-- The four SYM key ports and the cell port 109. -/
def symKeyPorts : Finset (Fin 254) := {109, 140, 141, 142, 143}

/-- The 17 request-level source words (`T = |input|`, `native`, `mask` the request's own fields, `N c` the SYM
drivers `driverLen r c`). -/
def symSrc (q T : Nat) (native mask : List Bool) (N : Fin 4 → Nat) : Fin 17 → List Bool :=
  ![List.replicate (T+1) true, frame (SignedSortKey.binary (T+1) 0),
    List.replicate (P1Closure.HardwireBudget.C (T+1)) true, CompareMachine.word q, CompareMachine.word 0,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.R T q (T+1)) true,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.U T q (T+1)) true, mask,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.H T q (T+1)) true, native,
    frame (SignedSortKey.binary (T+3) 0), CompareMachine.word (N 0), CompareMachine.word (N 1),
    CompareMachine.word (N 2), CompareMachine.word (N 3), CompareMachine.word 4,
    frame (SignedSortKey.binary (T+3) 4)]

/-- Which source word each SYM master port receives (`none` = blank). -/
def symSel (i : Fin 254) : Option (Fin 17) :=
  match i.val with
  | 2 => some 0 | 3 => some 1 | 4 => some 2 | 5 => some 3 | 111 => some 3
  | 6 => some 4 | 122 => some 4 | 7 => some 5 | 105 => some 6 | 108 => some 7 | 112 => some 8 | 124 => some 9
  | 128 => some 10 | 129 => some 10 | 130 => some 10 | 131 => some 10 | 132 => some 10
  | 135 => some 11 | 136 => some 12 | 137 => some 13 | 138 => some 14 | 139 => some 15 | 144 => some 16
  | _ => none

/-- One port of the table: evaluate the SYM input at the literal port, reduce the table, close with the pad lemmas. -/
macro "sym_port" : tactic => `(tactic| first
  | (bank_nf RowsConstruction.SymVerdict.input <;>
      simp (disch := first | assumption | (intro hne; exact absurd hne (by decide))) only [symSel, symSrc, Option.elim, Matrix.cons_val, ZeroPadding.pad_zero,
        MasterFan.pad_rep, MasterFan.pad_pad', MasterFan.word0] <;> rfl))

section Chunks
variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (I : Finset (Fin r.q)) (x : BitInput r.q)
  (L target T Dc cap R : Nat) (offset : Fin r.circuits.length → Nat)
  (hH : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) + 1 ≤ R)
  (hU : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) + 1 ≤ R)
  (hD : Dc ≤ R) (hc : cap ≤ R)

/-- The claim at one port. -/
def FanAt (i : Fin 254) : Prop :=
  ZeroPadding.pad R (SymVerdict.input r I x L target T (T+3) Dc cap offset i) =
    ZeroPadding.pad R ((symSel i).elim []
      (symSrc r.q T (PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r))
        (List.ofFn fun j => decide (j ∈ I)) (SymVerdict.N r)))

include hH hU hD hc

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan0 (v : Nat) (hv : v < 254) (hlo : 0 ≤ v) (hhi : v < 32) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan1 (v : Nat) (hv : v < 254) (hlo : 32 ≤ v) (hhi : v < 64) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan2 (v : Nat) (hv : v < 254) (hlo : 64 ≤ v) (hhi : v < 96) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan3 (v : Nat) (hv : v < 254) (hlo : 96 ≤ v) (hhi : v < 128) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan4 (v : Nat) (hv : v < 254) (hlo : 128 ≤ v) (hhi : v < 160) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan5 (v : Nat) (hv : v < 254) (hlo : 160 ≤ v) (hhi : v < 192) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan6 (v : Nat) (hv : v < 254) (hlo : 192 ≤ v) (hhi : v < 224) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
theorem fan7 (v : Nat) (hv : v < 254) (hlo : 224 ≤ v) (hhi : v < 254) (hi : (⟨v, hv⟩ : Fin 254) ∉ symKeyPorts) :
    FanAt r I x L target T Dc cap R offset ⟨v, hv⟩ := by
  unfold FanAt
  have hUR : PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) ≤ R := Nat.le_of_succ_le hU
  have hHR : PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) ≤ R := Nat.le_of_succ_le hH
  interval_cases v <;> first | (exfalso; apply hi; simp [symKeyPorts, Fin.ext_iff]; done) | sym_port

/-- **The SYM verdict input, padded to `R`, is the fanout table** at every non-key port. -/
theorem sym_fan_eq (i : Fin 254) (hi : i ∉ symKeyPorts) : FanAt r I x L target T Dc cap R offset i := by
  obtain ⟨v, hv⟩ := i
  by_cases h1 : v < 128
  · by_cases h2 : v < 64
    · by_cases h3 : v < 32
      · exact fan0 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h3 hi
      · exact fan1 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h2 hi
    · by_cases h3 : v < 96
      · exact fan2 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h3 hi
      · exact fan3 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h1 hi
  · by_cases h2 : v < 192
    · by_cases h3 : v < 160
      · exact fan4 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h3 hi
      · exact fan5 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h2 hi
    · by_cases h3 : v < 224
      · exact fan6 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) h3 hi
      · exact fan7 r I x L target T Dc cap R offset hH hU hD hc v hv (by omega) hv hi

end Chunks

/-! ## The sources for every request -/

/-- The SYM driver length of slot `c` (`0` off SYM). -/
def dlv (c : Nat) : PCJd4d1d9d7d1fa4313_Production.Request → Nat
  | .sym r _ _ _ => SymMeaning.driverLen r c
  | _ => 0

/-- **The 17 request-level source words**, for EVERY request (what one fixed machine computes). -/
def symSrcOf (a : DecompositionAlgorithm) (r : PCJd4d1d9d7d1fa4313_Production.Request) : Fin 17 → List Bool :=
  symSrc r.q (r.input a).length r.nativeWord
    (PCJ9eff70d512234a4c_Fixed.CyclicChoice.mask (r.family a).occurrences r.liveScale) (fun c => dlv c.val r)

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- At a SYM request the source words are `sym_fan_eq`'s. -/
theorem symSrcOf_sym :
    symSrcOf a (.sym r four L target) =
      symSrc r.q (symT a r four L target)
        (PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r))
        (List.ofFn fun j => decide (j ∈ symLive r L)) (SymVerdict.N r) := by
  rw [SymMeaning.native_eq r four L target]
  rfl

/-- **Every non-key master of `symMasters R k` is the padded fanout word** (109 included), at `R = symRes q T`. -/
theorem master_fan (k : RCFive.RowKeys.SymKey r L target) (i : Fin 254) (hi : i ∉ symKeyPorts ∨ i = 109) :
    symMasters a r four L target (symRes r.q (symT a r four L target)) k i =
      ZeroPadding.pad (symRes r.q (symT a r four L target))
        ((symSel i).elim [] (symSrcOf a (.sym r four L target))) := by
  have hR := symR_le_res r.q (symT a r four L target)
  unfold symR symLmax at hR
  by_cases h109 : i = 109
  · subst h109
    simp [symMasters, symSel, ZeroPadding.pad]
  · have hk : i ∉ symKeyPorts := by
      rcases hi with h | h
      · exact h
      · exact absurd h h109
    have hks : i ∉ symKeySet := by
      intro h
      apply hk
      simp only [symKeySet, Finset.mem_insert, Finset.mem_singleton] at h
      simp only [symKeyPorts, Finset.mem_insert, Finset.mem_singleton]
      omega
    have e := sym_fan_eq r (symLive r L) (fun _ => false) L target (symT a r four L target)
      (2*(symT a r four L target+3)+1) (symCap r.q (symT a r four L target)) (symRes r.q (symT a r four L target))
      k.offset (by omega) (by omega) (by omega) (by omega) i hk
    unfold FanAt at e
    rw [symSrcOf_sym a r four L target, ← e]
    simp only [symMasters, if_neg h109, keyPad, if_neg hks]

end Sym

/-! ## The fanout -/

/-- The 509 destinations: 254 cells (blank), 254 masters (`symSel`), the aux bits tape (blank). -/
def fanSel (i : Fin 509) : Option (Fin 17) :=
  if h : 254 ≤ i.val ∧ i.val < 508 then symSel ⟨i.val - 254, by omega⟩ else none

/-- The fanout's local tape of destination `i`. -/
def dst (i : Fin 509) : Fin (17+(509+1)+1) := ((i.castAdd 1).natAdd 17).castAdd 1
/-- Its local tape of source `j`. -/
def src (j : Fin 17) : Fin (17+(509+1)+1) := (j.castAdd (509+1)).castAdd 1
/-- The driver (the cell bank's clock) and the log (the cell bank's log). -/
def drvT : Fin (17+(509+1)+1) := ((0 : Fin 1).natAdd 509 |>.natAdd 17).castAdd 1
def logT : Fin (17+(509+1)+1) := (0 : Fin 1).natAdd (17+(509+1))

theorem fan_run (data : Fin 17 → List Bool) (R : Nat) (hD : ∀ j, (data j).length ≤ R) :
    Step (ExtIncidence.NativeFanout.machine fanSel) (2*R+4) (fun _ => 0)
      (ExtIncidence.NativeFanout.input data R) (fun _ => 0) (ExtIncidence.NativeFanout.output fanSel data R) :=
  Step.of_ready (ExtIncidence.NativeFanout.ready fanSel data R hD)

variable (data : Fin 17 → List Bool) (R : Nat)

theorem in_dst (i : Fin 509) : ExtIncidence.NativeFanout.input data R (dst i) = [] := by
  simp [ExtIncidence.NativeFanout.input, dst]
theorem in_src (j : Fin 17) : ExtIncidence.NativeFanout.input data R (src j) = data j := by
  simp [ExtIncidence.NativeFanout.input, src]
theorem in_drv : ExtIncidence.NativeFanout.input data R drvT = List.replicate R true := by
  simp only [ExtIncidence.NativeFanout.input, drvT, Fin.addCases_left, Fin.addCases_right]
theorem in_log : ExtIncidence.NativeFanout.input data R logT = [] := by
  simp only [ExtIncidence.NativeFanout.input, logT, Fin.addCases_right]

theorem out_dst (i : Fin 509) : ExtIncidence.NativeFanout.output fanSel data R (dst i) =
    ZeroPadding.pad R ((fanSel i).elim [] data) := by
  simp [ExtIncidence.NativeFanout.output, dst, ExtIncidence.NativeFanout.word]
theorem out_drv : ExtIncidence.NativeFanout.output fanSel data R drvT = List.replicate R true := by
  simp only [ExtIncidence.NativeFanout.output, drvT, Fin.addCases_left, Fin.addCases_right]
theorem out_log : ExtIncidence.NativeFanout.output fanSel data R logT = List.replicate (R+1) false := by
  simp only [ExtIncidence.NativeFanout.output, logT, Fin.addCases_right]

/-- Cells and the aux bits tape come out `0^R`. -/
theorem out_blank (i : Fin 509) (hi : i.val < 254 ∨ i.val = 508) :
    ExtIncidence.NativeFanout.output fanSel data R (dst i) = List.replicate R false := by
  rw [out_dst]
  have hn : fanSel i = none := by
    unfold fanSel
    rw [dif_neg (by omega)]
  rw [hn]
  simp [ZeroPadding.pad]

/-- The master destinations carry the padded table word. -/
theorem out_master (k : Fin 254) :
    ExtIncidence.NativeFanout.output fanSel data R (dst ⟨254+k.val, by omega⟩) =
      ZeroPadding.pad R ((symSel k).elim [] data) := by
  rw [out_dst]
  unfold fanSel
  rw [dif_pos (by simp only; omega)]
  congr 3
  exact Fin.ext (by simp only; omega)

end
end RowsInit.SymLoopFan
