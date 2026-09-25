import Proof.SourceAssembly.SourceStepsStartHole

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section inv4
open NearCubicWires.SourceConstruction.InitRun

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

def entryInvAt4 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (ph : Phase) (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) : Prop :=
  entryInvAt3 sources p den hden k r scratch n x bits hp E EF ph ci A H ∧
  (ph = .penalty ∧ ci = 0 → (queriedAt sources p den hden k r scratch n x bits hp ci A (E.whole E.q284)).length ≤ (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))

/-- `entryInvAt4` gives `entryInvAt3`. -/
theorem entryInvAt4_to3 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry) (ph : Phase) (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h : entryInvAt4 sources p den hden k r scratch n x bits hp E EF ph ci A H) : entryInvAt3 sources p den hden k r scratch n x bits hp E EF ph ci A H :=
  h.1

/-- At a successor clause `entryInvAt3` gives `entryInvAt4` (`ClauseParts.next`, `NextHole`). -/
theorem entryInvAt4_succ (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry) (ph : Phase) (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (h : entryInvAt3 sources p den hden k r scratch n x bits hp E EF ph (ci+1) A H) : entryInvAt4 sources p den hden k r scratch n x bits hp E EF ph (ci+1) A H :=
  ⟨h, fun h' => absurd h'.2 (Nat.succ_ne_zero ci)⟩

def Pen0Hole4 (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry) : Prop :=
  entryInvAt4 sources p den hden k r scratch n x bits hp E EF .penalty 0 (penaltyA0 sources p den hden k r scratch n x bits hp)
    (fun j => PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j))

theorem pen0Hole4_of (E : EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List CloseoutRowsEstimatorCoefficients.Stream.Entry) (h : Pen0Hole sources p den hden k r scratch n x bits hp E EF)
    (h284 : (queriedAt sources p den hden k r scratch n x bits hp 0 (penaltyA0 sources p den hden k r scratch n x bits hp) (E.whole E.q284)).length ≤ (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    Pen0Hole4 sources p den hden k r scratch n x bits hp E EF :=
  ⟨h, fun _ => h284⟩

end inv4

section start
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒽" => UOf_le mask packets rows sources res p k r
set_option hygiene false in
local notation "𝒞" => skelCodeR mask packets rows sources res hres p k r ph (refill3 mask packets rows sources res p k r se sp e (g7F ph).2) (preFF ph)
set_option hygiene false in
local notation "codeF" => fun ph' => skelCodeR mask packets rows sources res hres p k r ph' (refill3 mask packets rows sources res p k r se sp e (g7F ph').2) (preFF ph')
set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "layA" => layoutAtOf sources selector coordC ph ci L tgtC modeC lay
set_option hygiene false in
local notation "factsA" => factsAtOf sources selector compiler coordC ph ci L tgtC modeC
set_option hygiene false in
local notation "vWS" => P1TopDownPaidReusableReserves.workspace (printerOf sources) V
set_option hygiene false in
local notation "vRW" => P1TopDownPaidReusableReserves.rewind (printerOf sources) V
set_option hygiene false in
local notation "vBF" => P1TopDownPaidReusableReserves.buffer V
set_option hygiene false in
local notation "vMB" => InitRun.Mb L vQ
set_option hygiene false in
local notation "vMS" => InitPost.Ms L vQ
set_option hygiene false in
local notation "vU0" => InitRun.U0 L vQ
set_option hygiene false in
local notation "vdS" => clauseVals mask selector packets rows compiler sources p den hden k r (scratchOf mask packets rows sources res) n x bits hp site codeF ph ci L lay (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt (InitRun.D0 b) (InitRun.cap0 b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) (fun j => if j = 0 then w0 else oldAt coordC ph ci sources L tgtC modeC b (InitRun.D0 b) j) Hd Ad Rc familyCost refillCost firstCost counterReserve

end start

end
end NearCubicWires.SourceSteps
end

