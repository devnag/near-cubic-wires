import Proof.Packets.BudgetSeamScalars
import Proof.SourceAssembly.SourceStepsClassR
import Proof.SourceAssembly.SourceStepsHw

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- The site's call request is AD's admitted request of the same atoms. -/
theorem monomialRequest_eq_admitted (L target : Nat) (mode : Bool) {q : Nat} {circuit : BooleanCircuit q}
    {pcpp : PointwisePCPP circuit} (atoms : List (C10TotalDecode.Atom pcpp)) (four four' : atoms.length ≤ 4) :
    SourceRequest.monomialRequest L target mode atoms four = Admission.admittedRequest mode atoms four' L target := by
  cases mode <;> rfl

/-- **The packet writer's raw word fits its budget plus one** (the output tape starts empty and gains at most one cell per step). -/
theorem raw_length_le {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} (w : PacketWriter selector a)
    (r : PCJd4d1d9d7d1fa4313_Production.Request) :
    (r.raw selector a).length ≤ packetBudget a w.coefficient w.degree r + 1 := by
  obtain ⟨A, hstep, hout⟩ := PacketWriter.run selector a w r
  have h0 : (w.ordinary.program.inputTapes (r.input a) w.ordinary.program.outputTape).length ≤
      packetBudget a w.coefficient w.degree r + 1 := by
    unfold RepairOrdinary.Program.inputTapes
    rw [if_neg w.ordinary.program.outputFresh]
    exact Nat.zero_le _
  have h := RepairOrdinary.CloseoutFinalC10BandRecycle.band_length_at_cost _ _ hstep w.ordinary.program.outputTape rfl h0
  rw [hout] at h
  exact h

section clause
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)

set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp

/-- **The size facts of the site's call `m`** (every `m`, the terminal empty request included), past `inputCutoff`. -/
theorem site_call_facts (hden1 : 1 ≤ den) (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (m : Nat) :
    Admission.RequestAdmitted den p.clauseDegree (SourceBudget.tgt sources p) (requestAt coordC ph ci L tgtC modeC m) ∧
    (requestAt coordC ph ci L tgtC modeC m).q = C10PartsSchedule.widthAt sources k n ∧
    (requestAt coordC ph ci L tgtC modeC m).liveScale = L := by
  have hadm := Admission.trace_atoms_admitted sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits hcut ph ci
    (TraceData.order coordC ph ci) (List.Perm.refl _) m
  have hf : ((TraceData.order coordC ph ci).map (fun mo => mo.factors)).getD m [] = SourceRequest.FactorLoop.factorsAt coordC ph ci m := by
    by_cases hlt : m < (TraceData.order coordC ph ci).length
    · exact TraceData.factors_getD coordC ph ci m hlt
    · have h1 : ((TraceData.order coordC ph ci).map (fun mo => mo.factors)).getD m [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl
      have hlen : (monomials coordC ph ci).length = (TraceData.order coordC ph ci).length := rfl
      have h2 : SourceRequest.FactorLoop.factorsAt coordC ph ci m = [] := by
        unfold SourceRequest.FactorLoop.factorsAt
        rw [List.getElem?_eq_none (by omega)]
      rw [h1, h2]
  have hadm' : Admission.Admitted den p.clauseDegree (SourceRequest.FactorLoop.factorsAt coordC ph ci m) :=
    (congrArg (Admission.Admitted den p.clauseDegree) hf).mp hadm
  have heq : requestAt coordC ph ci L tgtC modeC m =
      Admission.admittedRequest modeC (SourceRequest.FactorLoop.factorsAt coordC ph ci m) hadm'.four L tgtC :=
    monomialRequest_eq_admitted L tgtC modeC _ _ hadm'.four
  rw [heq]
  refine ⟨hadm'.requestAdmitted hden1 modeC L tgtC, ?_, Admission.admittedRequest_liveScale _ _ _ _ _⟩
  rw [Admission.admittedRequest_q]
  exact Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x oracleC hcut

end clause

end
end NearCubicWires.SourceSteps
end
