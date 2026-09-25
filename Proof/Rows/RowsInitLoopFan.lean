import Proof.Rows.RowsInitMasterFan

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.LoopFan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open RowsConstruction RowsConstruction.BaseLayout RowsInit.MasterFan
noncomputable section

/-- The circuit count of a request (`0` on the terminal sentinel). -/
def circOf : PCJd4d1d9d7d1fa4313_Production.Request → Nat
  | .terminal => 0
  | .sym r _ _ _ => r.circuits.length
  | .thr r _ _ _ => r.circuits.length

/-- **The 23 request-level source words**, for EVERY request (what one fixed machine computes). -/
def srcOf (a : DecompositionAlgorithm) (r : PCJd4d1d9d7d1fa4313_Production.Request) : Fin 23 → List Bool :=
  thrSrc r.q (r.input a).length (ThrBounds.UOf thrCU thrDU r.q (r.input a).length)
    (ThrBounds.FOf thrCF thrDF r.q (r.input a).length) (circOf r) r.nativeWord
    (PCJ9eff70d512234a4c_Fixed.CyclicChoice.mask (r.family a).occurrences r.liveScale) (frame (r.topWord a))

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- At a THR request the source words are `thr_fan_eq`'s, at any selection. -/
theorem srcOf_thr (sel : ThresholdRows.Selection a r) :
    srcOf a (.thr r four L target) =
      thrSrc r.q (ThrWidth.T a r four L target) (Uf r.q (ThrWidth.T a r four L target))
        (Ff r.q (ThrWidth.T a r four L target)) (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count
        (PCJ45bee56da9f34d5a_StreamPair.native r L target) (List.ofFn fun j => decide (j ∈ thrLive r L))
        (frame ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.flatMap frame)) := by
  rw [PCJ45bee56da9f34d5a_StreamPair.native_eq r four L target, ThrBounds.words_eq a r four sel, List.flatMap_map]
  rfl

/-- **Every non-key master of `thrMasters R k` is the padded fanout word** (109 included). -/
theorem master_fan (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 254) (hi : i ∉ keyPorts ∨ i = 109) :
    thrMasters a r four L target (thrRes r.q (ThrWidth.T a r four L target)) k i =
      ZeroPadding.pad (thrRes r.q (ThrWidth.T a r four L target)) ((thrSel i).elim [] (srcOf a (.thr r four L target))) := by
  have hR := thrR_le_res r.q (ThrWidth.T a r four L target)
  unfold thrR thrLmax at hR
  by_cases h109 : i = 109
  · subst h109
    simp [thrMasters, thrSel, ZeroPadding.pad]
  · have hk : i ∉ keyPorts := by
      rcases hi with h | h
      · exact h
      · exact absurd h h109
    have hks : i ∉ thrKeySet := by
      intro h
      apply hk
      simp only [thrKeySet, Finset.mem_insert, Finset.mem_singleton] at h
      simp only [keyPorts, Finset.mem_insert, Finset.mem_singleton]
      omega
    have e := thr_fan_eq a r four k.selection (thrLive r L) k.prime k.residue (ThrWidth.T a r four L target) L target
      (Uf r.q (ThrWidth.T a r four L target)) (Ff r.q (ThrWidth.T a r four L target))
      (thrRes r.q (ThrWidth.T a r four L target))
      (by unfold PCJ45bee56da9f34d5a_UniformMinimumBounds.H at hR ⊢; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) i hk
    rw [srcOf_thr a r four L target k.selection, ← e]
    simp only [thrMasters, if_neg h109, keyPad, if_neg hks]

end Thr

/-! ## The fanout -/

/-- The 509 destinations: 254 cells (blank), 254 masters (`thrSel`), the aux bits tape (blank). -/
def fanSel (i : Fin 509) : Option (Fin 23) :=
  if h : 254 ≤ i.val ∧ i.val < 508 then thrSel ⟨i.val - 254, by omega⟩ else none

/-- The fanout's local tape of destination `i`. -/
def dst (i : Fin 509) : Fin (23+(509+1)+1) := ((i.castAdd 1).natAdd 23).castAdd 1
/-- Its local tape of source `j`. -/
def src (j : Fin 23) : Fin (23+(509+1)+1) := (j.castAdd (509+1)).castAdd 1
/-- The driver (the cell bank's clock) and the log (the cell bank's log). -/
def drvT : Fin (23+(509+1)+1) := ((0 : Fin 1).natAdd 509 |>.natAdd 23).castAdd 1
def logT : Fin (23+(509+1)+1) := (0 : Fin 1).natAdd (23+(509+1))

theorem fan_run (data : Fin 23 → List Bool) (R : Nat) (hD : ∀ j, (data j).length ≤ R) :
    Step (ExtIncidence.NativeFanout.machine fanSel) (2*R+4) (fun _ => 0)
      (ExtIncidence.NativeFanout.input data R) (fun _ => 0) (ExtIncidence.NativeFanout.output fanSel data R) :=
  Step.of_ready (ExtIncidence.NativeFanout.ready fanSel data R hD)

variable (data : Fin 23 → List Bool) (R : Nat)

theorem in_dst (i : Fin 509) : ExtIncidence.NativeFanout.input data R (dst i) = [] := by
  simp [ExtIncidence.NativeFanout.input, dst]
theorem in_src (j : Fin 23) : ExtIncidence.NativeFanout.input data R (src j) = data j := by
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
      ZeroPadding.pad R ((thrSel k).elim [] data) := by
  rw [out_dst]
  unfold fanSel
  rw [dif_pos (by simp only; omega)]
  congr 3
  exact Fin.ext (by simp only; omega)

end
end RowsInit.LoopFan
