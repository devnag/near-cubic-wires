import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.MachineModel.CanonicalFourfoldRowProgram

/-! A bounded test of the paper's occurrence-preserving route. Literal raw
GF2 substitution needs no cancellation for BinLift correctness. Its actual
length supplies the row digit bound; final mode/onset instantiation remains
separate from this constructor-for-constructor calculation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawOccurrenceBound
open CanonicalFourfoldRowProgram
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem mul_length (left right : StructuralGF2Polynomial) :
    (structuralGF2Mul left right).length=left.length*right.length := by
  induction left with
  | nil => simp [structuralGF2Mul]
  | cons m left ih =>
    simp only [structuralGF2Mul,List.flatMap_cons,List.length_append,List.length_map,List.length_cons] at *
    nlinarith

end NearCubicWires.RepairOrdinary.CloseoutRowsRawOccurrenceBound
