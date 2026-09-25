import Proof.Rows.UniformGateCell

/-! Full-assignment evaluator with shared uniform R and retained-master padding. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_UniformFullGate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure NearCubicWires.ExtIncidence
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open PCJ45bee56da9f34d5a_FullGateRun (masterCaps pad_cold)
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine
def palette {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (w H R : Nat) :=
  words (ZeroPadding.pad H (source g)) (ZeroPadding.pad H (List.ofFn x)) q w (HardwireBudget.C w) (R)
def budget {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (w R U : Nat) :=
  2*OffsetSourceGate.budget (OffsetSourceGate.items g x) (g.threshold-1) w (HardwireBudget.C w)+4*R+4*U+30

theorem run {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (out : List Bool) (w H R U : Nat)
    (hw : 0 < w) (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w)
    (hcap : PCJ45bee56da9f34d5a_FullGateBounds.reserve g x w ≤ R)
    (hc : HardwireBudget.C w+1 ≤ U) (hd : HardwireBudget.D q w ≤ U)
    (hr : R+1 ≤ U)
    (hu : ∀i,(words (source g) (List.ofFn x) q w (HardwireBudget.C w) (R) i).length ≤ U) :
    Step PCJ45bee56da9f34d5a_CellGate.machine (budget g x w R U)
      (heads out 0) (cold (palette g x w H R) U out)
      (heads (out++[g.eval x]) 0) (cold (palette g x w H R) U (out++[g.eval x])) := by
  have hi : (OffsetSourceGate.items g x).length=q := List.length_ofFn
  obtain ⟨hf,hp,hn,hz,hpt,hnt⟩ := of_magnitude g x w hw hm
  have h := (PCJ45bee56da9f34d5a_UniformGateCell.run (OffsetSourceGate.items g x) (g.threshold-1) [] [] out w
    (HardwireBudget.C w) (HardwireBudget.D q w) R U hf le_rfl hp hn (score_loop g x w).le hz hpt hnt hc hd hr hcap
    (by simpa only [OffsetSourceGate.items_word,OffsetSourceGate.items_mask,hi,List.append_nil,source,reserve] using hu)).pad (masterCaps H)
  simpa only [OffsetSourceGate.items_word,OffsetSourceGate.items_mask,hi,List.append_nil,
    OffsetSourceGate.bit_eval,source,reserve,pad_cold,palette,budget] using h
end
end PCJ45bee56da9f34d5a_UniformFullGate
