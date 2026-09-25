import Proof.Rows.FullGateRun

/-! One noncircular polynomial cleanup reserve, independent of false padding
on the retained original source and minimizing assignment. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
namespace PCJ45bee56da9f34d5a_FullGateCapacity
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open scoped BigOperators
noncomputable section

def capacity (B q w : Nat) := 2048*(B+q+w+1)^2

theorem fits {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) (B w : Nat)
    (hw : 0 < w) (hb : (source g).length ≤ B)
    (hm : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs) < 2^w) :
    HardwireBudget.C w+1 ≤ capacity B q w ∧
    HardwireBudget.D q w ≤ capacity B q w ∧
    reserve g x w+1 ≤ capacity B q w ∧
    ∀i,(words (source g) (List.ofFn x) q w (HardwireBudget.C w) (reserve g x w) i).length ≤ capacity B q w := by
  have hr := reserve_bound g x B w hw hb hm
  have hsq : B+q+w+1 ≤ (B+q+w+1)^2 := Nat.le_self_pow (by decide) _
  have hsq1 : 1 ≤ (B+q+w+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hc : HardwireBudget.C w+1 ≤ capacity B q w := by unfold HardwireBudget.C capacity;nlinarith
  have hd : HardwireBudget.D q w ≤ capacity B q w := by unfold HardwireBudget.D HardwireBudget.C capacity;nlinarith
  have hR : reserve g x w+1 ≤ capacity B q w := by unfold capacity;omega
  refine ⟨hc,hd,hR,?_⟩
  intro i;fin_cases i <;>simp [words,frame_length,SignedSortKey.binary_length,CompareMachine.word]
  all_goals unfold capacity at *;nlinarith

end
end PCJ45bee56da9f34d5a_FullGateCapacity
