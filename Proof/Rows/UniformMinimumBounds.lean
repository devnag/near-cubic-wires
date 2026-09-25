import Proof.Rows.UniformMinimumGate
import Proof.Rows.FullGateCapacity

/-! Uniform paid banks across all original gates of one request. A short linear
source/parser cap H, a quadratic evaluator reserve R, and larger cleanup U are
separate; no tape capacity depends on itself. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000
namespace PCJ45bee56da9f34d5a_UniformMinimumBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open PCJ45bee56da9f34d5a_MinimumGateCell (minInput)
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_MinimumGateCell.machine

def H (B q w : Nat) := 64*(B+q+w+1)
def R (B q w : Nat) := 1024*(B+q+w+1)^2
def U := PCJ45bee56da9f34d5a_FullGateCapacity.capacity

theorem run {q : Nat} (g : NormalizedThresholdGate q) (live : Finset (Fin q)) (x : BitInput q)
    (out : List Bool) (B w : Nat) (hw : 0 < w) (hb : (source g).length ≤ B)
    (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w) :
    Step PCJ45bee56da9f34d5a_MinimumGateCell.machine (65536*(B+q+w+1)^2)
      (PCJ45bee56da9f34d5a_MinimumGateCell.heads out)
      (PCJ45bee56da9f34d5a_UniformMinimumGate.bank g live x w (H B q w) (R B q w) (U B q w) [] out)
      (PCJ45bee56da9f34d5a_MinimumGateCell.heads (out++[residualConstant g live x]))
      (PCJ45bee56da9f34d5a_UniformMinimumGate.bank g live x w (H B q w) (R B q w) (U B q w) [] (out++[residualConstant g live x])) := by
  have hcap := reserve_bound g (minInput g live x) B w hw hb hm
  obtain ⟨hc,hd,_,_⟩:=PCJ45bee56da9f34d5a_FullGateCapacity.fits g (minInput g live x) B w hw hb hm
  have hsq : 1 ≤ (B+q+w+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hr : R B q w+1 ≤ U B q w := by unfold R U PCJ45bee56da9f34d5a_FullGateCapacity.capacity;omega
  have hsq' : B+q+w+1 ≤ (B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hu : ∀i,(words (source g) (List.ofFn (minInput g live x)) q w (HardwireBudget.C w) (R B q w) i).length ≤ U B q w := by
    intro i
    fin_cases i <;>simp [words,frame_length,SignedSortKey.binary_length,CompareMachine.word]
    all_goals unfold R U PCJ45bee56da9f34d5a_FullGateCapacity.capacity at *;nlinarith
  have hs : ((List.ofFn g.weight).flatMap intWord).length ≤ H B q w := by
    unfold source at hb;simp only [List.length_append] at hb;unfold H;omega
  have h := PCJ45bee56da9f34d5a_UniformMinimumGate.run g live x out w (H B q w) (R B q w) (U B q w)
    hw hm (by unfold H;omega) hs (by unfold H;omega) hc hd hr hcap hu
  apply h.enlarge
  have hg := worker_bound g (minInput g live x) w hw hm
  unfold PCJ45bee56da9f34d5a_MinimumMaskRun.budget PCJ45bee56da9f34d5a_UniformFullGate.budget
    H R U PCJ45bee56da9f34d5a_FullGateCapacity.capacity
  nlinarith
end
end PCJ45bee56da9f34d5a_UniformMinimumBounds
