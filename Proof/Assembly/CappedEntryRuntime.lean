import Proof.MachineModel.ControllerCappedRuntime

namespace PCJ644510ff491048c3_
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces
open NearCubicWires.P1TopDown
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

def entryCoefficient (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r : Nat) : Nat :=
  Classical.choose (WorkspaceSelectedEntryRuntime.entry_bound sources p
    (ControllerCappedRuntime.hierarchyIndex sources p den remainingDegree) r)

def entryOnset (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r : Nat) : Nat :=
  Classical.choose (Classical.choose_spec (WorkspaceSelectedEntryRuntime.entry_bound sources p
    (ControllerCappedRuntime.hierarchyIndex sources p den remainingDegree) r))

def coefficient (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r remainingCoefficient : Nat) : Nat :=
  entryCoefficient sources p den remainingDegree r + remainingCoefficient

def onset (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r remainingOnset : Nat) : Nat :=
  max (entryOnset sources p den remainingDegree r) remainingOnset

theorem bounds (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den remainingDegree r base scratch : Nat)
    (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      Machine (ControllerSelectedContinuation.bodyTapes sources p
        (ControllerCappedRuntime.hierarchyIndex sources p den remainingDegree) r scratch) states)
    (remainingFuel : Nat → Nat) (remainingCoefficient remainingOnset tableCoefficient tableDegree : Nat)
    (hremaining : let C := ControllerCappedRuntime.continuation sources p den remainingDegree r base scratch site remainingFuel
      ∀ n, remainingOnset≤n → remainingFuel n+3≤remainingCoefficient*(n+1)^remainingDegree+
        tableCoefficient*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree+2)*
          SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^tableDegree)) :
    let C := ControllerCappedRuntime.continuation sources p den remainingDegree
      r base scratch site remainingFuel;
    max (ControllerCappedRuntime.prepDegree sources p den)
      (WorkspaceSelectedEntryRuntime.degree sources p remainingDegree)≤C.k+1 ∧
    ∀ n,onset sources p den remainingDegree r remainingOnset≤n →
      C.fuel n+2≤coefficient sources p den remainingDegree r remainingCoefficient*
        (n+1)^(WorkspaceSelectedEntryRuntime.degree sources p remainingDegree)+
      tableCoefficient*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree+2)*
        SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^tableDegree) := by
  let k := ControllerCappedRuntime.hierarchyIndex sources p den remainingDegree
  let C := ControllerCappedRuntime.continuation sources p den remainingDegree
    r base scratch site remainingFuel
  change max (ControllerCappedRuntime.prepDegree sources p den)
    (WorkspaceSelectedEntryRuntime.degree sources p remainingDegree)≤C.k+1 ∧ _
  constructor
  · change k≤k+1
    omega
  · intro n hn
    have hentry := Classical.choose_spec (Classical.choose_spec
      (WorkspaceSelectedEntryRuntime.entry_bound sources p k r)) n
    change entryOnset sources p den remainingDegree r≤n →
      WorkspaceSelectedEntryBudget.envelope sources p k r n≤
        entryCoefficient sources p den remainingDegree r*
          (n+1)^WorkspaceSelectedEntryRuntime.entryDegree sources p at hentry
    have he := hentry ((Nat.le_max_left _ _).trans hn)
    have hr := hremaining n ((Nat.le_max_right _ _).trans hn)
    have ep := Nat.mul_le_mul_left (entryCoefficient sources p den remainingDegree r)
      (Nat.pow_le_pow_right (by omega : 1≤n+1)
        (Nat.le_max_left (WorkspaceSelectedEntryRuntime.entryDegree sources p) remainingDegree))
    have rp := Nat.mul_le_mul_left remainingCoefficient
      (Nat.pow_le_pow_right (by omega : 1≤n+1)
        (Nat.le_max_right (WorkspaceSelectedEntryRuntime.entryDegree sources p) remainingDegree))
    change WorkspaceSelectedEntryBudget.envelope sources p k r n+1+remainingFuel n+2≤_
    unfold coefficient WorkspaceSelectedEntryRuntime.degree
    nlinarith

end
end PCJ644510ff491048c3_
