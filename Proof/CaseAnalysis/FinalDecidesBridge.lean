import Proof.CaseAnalysis.FinalOnset
import Proof.CaseAnalysis.FinalPipeline

namespace NearCubicWires.RepairSource.CloseoutFinal.C10Decides

open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open CompetitorSourceAverage AggregateSemanticStage SelectedRecoveryIntegration
open CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CloseoutFinal

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))

/-- The run receipt inside a verdict, in the shape `Weak.decides` asks for: acceptance
read off the verdict's exit tapes IS the scanned result bit of the machine's own run. -/
theorem decides_of_verdict {t st : Nat} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    {constants : Constants (selectedPCPP sources)} {pcpp : PointwisePCPP circuit}
    {proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {worker : LocalBitMultitape.Machine t st} {ht : 2 ≤ t} {fuel : Nat → Nat}
    {len : ℕ} {x : BitInput len} {bits : List Bool}
    {result : Fin t} {ports : CloseoutRowsOriginalSchedule.Phase → Fin t} {width : CloseoutRowsOriginalSchedule.Phase → ℕ}
    (V : Verdict constants pcpp proofValue evaluate worker ht fuel len x bits result ports width)
    (hbit : readTapeBit (V.exit result) (V.heads result) = true) :
    Weak.decides worker ht result fuel len x bits := by
  obtain ⟨r, hr, hheads, htapes, _hsteps⟩ := V.run
  refine ⟨r, hr, ?_⟩
  show readTapeBit (r.final.tapes result) (r.final.heads result) = true
  rw [htapes, hheads]
  exact hbit

end
end NearCubicWires.RepairSource.CloseoutFinal.C10Decides
