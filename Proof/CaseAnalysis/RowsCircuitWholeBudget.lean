import Proof.CaseAnalysis.RowsCircuitCapacity

/-! The complete cold circuit has one paid linear-in-capacity bound.
Actual list multiplicity is included; policy caps are read-only operands. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitWholeBudget
open LocalBitMultitape RepairSource.CloseoutSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem amount_bound (threshold : Bool) (D n : ℕ) :
    CloseoutRowsCircuitArithmeticDock.amount threshold D n ≤ D+n+2:=by
  cases threshold
  · exact Nat.div_le_self _ _
  · exact (Nat.div_le_self _ _).trans (by omega)

theorem arithmetic_bound (threshold : Bool) (D n : ℕ) :
    CloseoutRowsCircuitArithmeticDock.budget threshold D n ≤ 24*(D+n)+58:=by
  cases threshold
  · change CloseoutRowsCircuitSymmetricDescription.budget D n ≤ _
    rw [CloseoutRowsCircuitDescriptionMeaning.symmetric_budget]
    omega
  · change CloseoutRowsCircuitThresholdDescription.budget D n ≤ _
    have h:=CloseoutRowsCircuitDescriptionMeaning.threshold_budget D n
    omega

theorem symmetric_cold_bound (C : ℕ) (bits : List Bool)
    (hp : CloseoutRowsCircuitPrefix.budget bits+1 ≤ C)
    (ht : CloseoutRowsCircuitSymTop.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+1 ≤ C) :
    CloseoutRowsCircuitColdSymmetric.budget C bits ≤ 14*C+40:=by
  unfold CloseoutRowsCircuitColdSymmetric.budget CloseoutRowsCircuitColdEntry.budget
    CloseoutRowsCircuitSymmetricTop.budget
  omega

theorem threshold_cold_bound (C : ℕ) (bits : List Bool)
    (hp : CloseoutRowsCircuitPrefix.budget bits+1 ≤ C)
    (ht : 2*CloseoutRowsGateMeasured.budget (CloseoutRowsCircuitHeader.codeWord bits 3)+4 ≤ C) :
    CloseoutRowsCircuitColdThreshold.budget C bits ≤ 14*C+40:=by
  unfold CloseoutRowsCircuitColdThreshold.budget CloseoutRowsCircuitColdEntry.budget
    CloseoutRowsCircuitThresholdTop.budget
  omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitWholeBudget
