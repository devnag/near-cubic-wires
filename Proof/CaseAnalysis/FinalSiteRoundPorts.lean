import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRoundBudget

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPorts

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe (phaseRecords')
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower entryWidthSchedule)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank bankAt words_append)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 The two record ports, and the exact delta one site round owes them -/

/-- **One record occupies a fixed number of cells.**  `record_length`
(`Proof/CaseAnalysis/RowsEstimatorCoefficientsPrepare.lean`) at the six fields of
`entryWord` (`Proof/CaseAnalysis/RowsEstimatorCoefficientsLoop.lean`): the width is
a function of the bank width `b` ALONE, not of the record's numbers.  This is
what makes §2's offset identity possible. -/
theorem entryWord_length (b : ℕ) (a : Entry) :
    (CloseoutRowsEstimatorCoefficients.Stream.entryWord b a).length = 20 * b + 22 :=
  CloseoutRowsEstimatorCoefficients.Stream.record_length b a.coefficient a.count a.denominator

/-! ## §2 The append offset, in closed form -/

/-! ## §3 The bound that does not mention the round index -/

/-! ## §4 The round count is polynomial in `q` -/

/-! ## §5 The stage `roundFuel` omits, and the corrected round total -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPorts
