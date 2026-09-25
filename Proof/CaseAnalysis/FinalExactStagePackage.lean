import Proof.CaseAnalysis.FinalCompletion
import Proof.CaseAnalysis.FinalStageFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate
  stageMass)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal (constantsOf Parameters Runtime Theorem25Target
  theorem25_of_leaves)
open NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.RepairSource.CloseoutFinal.C10Fusion (Pipeline)
open NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdictUniform (tbud tailWidths'_of)
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (rowAnswer_le_rowDenominator)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ)

attribute [local irreducible] pcppOf Atoms

/-- **The stage's data at the paper's own per-call fraction.**  Field for field
`StageData` (`Proof/CaseAnalysis/FinalStageContracts.lean`), except that the pair
`answer : ... → List Atom → ℕ` (`:79`) and `denominator : ℕ → ℕ` (`:74`) is replaced
by the numerator/denominator pair `exactFractionRecord`
(`Proof/CaseAnalysis/FinalExactFraction.lean`) consumes: one pair per PCPP
clause address and monomial.  `den` is A.13.9's `|\mathcal E| 2 ^ q`
(`paper.tex:3161`), i.e. `rowDenominator`
(`Proof/CaseAnalysis/FinalSupplierAccuracy.lean`), which is a function of the
request and therefore cannot be a `ℕ → ℕ`. -/
structure StageData' {gamma : ℝ} (p : Parameters sources gamma) :
    Type 1 where
  e : ℕ
  st : Phase → ℕ
  stage : (ph : Phase) → LocalBitMultitape.Machine (218+e) (st ph)
  stageFuel : Phase → ℕ → ℕ
  entryWidth : ℕ → ℕ
  num : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ
  den : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ
  coordinate : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin ((pcppOf sources k p x bits).systematicBits+(pcppOf sources k p x bits).auxiliaryBits) →
      CircuitPolynomial (Atoms sources k p x bits) 1
  supplier : (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ
  failure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  mass : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  L : ℕ → ℕ
  budget : ℕ → ℕ

attribute [local semireducible] pcppOf Atoms

variable {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData' sources k p)

/-- The emitted record stream, at A.13.9's own fraction.  `records`
(`Proof/CaseAnalysis/FinalStageContracts.lean`) with `phaseRecords` replaced by
`phaseRecords'` (`Proof/CaseAnalysis/FinalExactFraction.lean`). -/
abbrev records' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  phaseRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits) Atom.systematic
    (exactFractionRecord (2 ^ (pcppOf sources k p x bits).clauseBits) (S.num n x bits)
      (S.den n x bits))

end

noncomputable section
variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData' sources k p)

/-! ## §6 The capstone anti-fork receipt -/

/-! **What is NOT compiled here, stated exactly.**  The three remaining data-level
identities -- `rawRealizes'` vs `rawRealizes`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`), `verdict_of_stage'` vs
`verdict_of_stage` (`:145`), and `machine_of_stage'` vs `machine_of_stage`
(`Proof/CaseAnalysis/FinalPipelineOfStage.lean`) -- are STATED at inputs this file
proves definitionally equal, but each was rejected by Lean as
`(deterministic) timeout at isDefEq` under the strict profile's 250000 heartbeats.
That is a budget fact about the size of the unfolding, not a counterexample, and
raising the limit is prohibited; the identities above `Realizes` are therefore
recorded as UNCHECKED rather than claimed. -/

attribute [local irreducible] stageNum stageDen stageRowSupplier stageMass stageCoordinate
  stageEntryWidth stageArity stageTarget stageFailure

/-- **The exact-fraction stage data**: A.13.9's own numerator over its own
`|\mathcal E| 2 ^ q` (`paper.tex:3161`), per call, at STAGEFIELDS' witnesses. -/
def exactStageData (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ) (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ) : StageData' sources k p where
  e := 60 + extra
  st := st
  stage := stage
  stageFuel := stageFuel
  entryWidth := stageEntryWidth sources k p coefficientFloor
  num := stageNum sources k p liveScale
  den := stageDen sources k p liveScale
  coordinate := stageCoordinate sources k p
  supplier := stageRowSupplier sources k p liveScale
  failure := fun n _ _ _ =>
    1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ)
  mass := stageMass sources k p
  L := L
  budget := budget

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
