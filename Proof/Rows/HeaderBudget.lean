import Proof.Rows.HeaderField

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_HeaderBudget
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open MatrixScoreBatch CloseoutRowsEstimator

/-- The cost of the actual scan is linear in its emitted header bytes,
including the empty-cut case. No square of the copy capacity is introduced. -/
theorem cut_length (p : Nat) (c : Cut) :
    (cutWord p c).length=(fields c).length*(2*p+3) := by
  simp [cutWord,List.length_flatMap,
    show 2*(p+1)+1=2*p+3 by omega]

theorem stream_length (row : EquationRow.Input) :
    (Header.stream row).length=
      row.cuts.length*(Scan.countFields row*(2*row.p+3)) := by
  have hm : row.cuts.map (fun c => (cutWord row.p c).length)=
      row.cuts.map (fun _ => Scan.countFields row*(2*row.p+3)) := by
    apply List.map_congr_left
    intro c hc
    rw [cut_length,Scan.row_fields row c hc]
  simp only [Header.stream,List.length_flatMap]
  rw [hm]
  simp

theorem ticks_le (row : EquationRow.Input) :
    Scan.ticks row ≤ 6*(Header.stream row).length+2 := by
  have fieldsPositive : 1 ≤ Scan.countFields row := by
    unfold Scan.countFields
    omega
  have count : row.cuts.length ≤ row.cuts.length*Scan.countFields row := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left row.cuts.length fieldsPositive
  have bytes : row.cuts.length*Scan.countFields row ≤ (Header.stream row).length := by
    rw [stream_length]
    simpa only [Nat.mul_one,Nat.mul_assoc] using
      Nat.mul_le_mul_left (row.cuts.length*Scan.countFields row)
        (show 1 ≤ 2*row.p+3 by omega)
  change (Header.stream row).length+
      row.cuts.length*(2*Scan.countFields row+3)+2 ≤ _
  nlinarith

theorem budget_le (row : EquationRow.Input) (K : Nat)
    (fits : (Header.stream row).length ≤ K) :
    PCJ45bee56da9f34d5a_HeaderField.budget row K ≤ 18*K+14 := by
  have scan := ticks_le row
  unfold PCJ45bee56da9f34d5a_HeaderField.budget
  omega

end PCJ45bee56da9f34d5a_HeaderBudget
