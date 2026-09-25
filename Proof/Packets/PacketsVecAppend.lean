import Proof.Packets.PacketsCoordHoles
import Proof.Packets.PacketsSeedDecode

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryBoundedTapeCopy

namespace Append

def cfg (src out : List Bool) (L : ℕ) (q : Fin 2) (d : ℕ) : Configuration 3 2 :=
  ⟨q, ![d, out.length + d, d], ![src, out ++ copied src d, List.replicate L true]⟩

theorem copy_step (src out : List Bool) (L d : ℕ) (hd : d < L) :
    step raw (cfg src out L 0 d) = some (cfg src out L 0 (d + 1)) := by
  have hread : readTapeBit (List.replicate L true) d = true := by simp [readTapeBit, List.getD, hd]
  simp only [step, raw, cfg, Configuration.scanned]
  simp [hread]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, HeadMove.apply]
    omega
  · funext i; fin_cases i <;> simp [applyAction]
    have hl : (out ++ copied src d).length = out.length + d := by simp
    have hw := Streaming.write_append (out ++ copied src d) (readTapeBit src d)
    rw [hl] at hw
    rw [hw, prefix_succ, List.append_assoc]

theorem stop_step (src out : List Bool) (L : ℕ) :
    step raw (cfg src out L 0 L) = some (cfg src out L 1 L) := by
  have hread : readTapeBit (List.replicate L true) L = false := by simp [readTapeBit, List.getD]
  simp only [step, raw, cfg, Configuration.scanned]
  simp [hread]
  rfl

theorem loop (src out : List Bool) (L m d : ℕ) (h : d + m = L) :
    Timed raw (m + 1) (cfg src out L 0 d) (cfg src out L 1 L) := by
  induction m generalizing d with
  | zero =>
    have hd : d = L := by omega
    subst hd
    exact Timed.single (by rfl) (stop_step src out d)
  | succ m ih =>
    exact Timed.step (by rfl) (copy_step src out L d (by omega)) (ih (d + 1) (by omega))

theorem append_run (src out : List Bool) (L : ℕ) :
    Step raw (L + 1) ![0, out.length, 0] ![src, out, List.replicate L true]
      ![L, out.length + L, L] ![src, out ++ copied src L, List.replicate L true] := by
  obtain ⟨r, hr, hf, _⟩ := (loop src out L L 0 (by omega)).run (by rfl)
  have hc : cfg src out L 0 0 = (⟨raw.start, ![0, out.length, 0], ![src, out, List.replicate L true]⟩ :
      Configuration 3 2) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [cfg, copied]
  rw [hc] at hr
  exact Step.of_run hr (by rw [hf]; rfl) (by rw [hf]; rfl)

theorem copied_pad (Q : ℕ) (v : List Bool) : copied (ZeroPadding.pad Q v) v.length = v := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [copied, List.getElem_map, List.getElem_range, readTapeBit, ZeroPadding.pad]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simp [h2]

end Append

section Stage
open NearCubicWires.PacketsConstruction.Residual

/-- Reset the source and driver heads, keep the output head. -/
def appendSel (i : Fin 3) : Bool := decide (i.val ≠ 1)

noncomputable def appendStage : AppendStage where
  extra := 1
  states := 2 + 2
  machine := MaskedReset.machine raw appendSel
  cost := fun n => 2 * (n + 1) + 2
  costC := 4
  costD := 1
  cost_le := fun n => by rw [pow_one]; omega
  run := fun Q v out _ => by
    have hs := Append.append_run (ZeroPadding.pad Q v) out v.length
    rw [Append.copied_pad] at hs
    obtain ⟨k, hm⟩ := readyMask hs appendSel (by intro i hi; fin_cases i <;> simp_all [appendSel])
    refine ⟨_, _, hm.congr_in ?_ ?_, ?_, ?_, ?_, ?_⟩
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · fin_cases j <;> rfl
      · simp
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]
        fin_cases j <;> simp [appendEntry]
      · simp [appendEntry]
    · rfl
    · change (if appendSel 1 then 0 else out.length + v.length) = _
      simp [appendSel]
    · rfl
    · rfl

end Stage

end NearCubicWires.PacketsSeed

