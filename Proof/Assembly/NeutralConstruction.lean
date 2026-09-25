import Proof.Assembly.NeutralSource

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native

namespace PCJf08f3457b0ab4c67_Neutral

/-- The exact accepted source-global physical-construction telescope. -/
noncomputable abbrev Construction : Prop :=
∃ (capIndex : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (remainingDegree : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (r : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (base : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (scratch : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat)),
∃ (site : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Bool → NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule.Phase → Σ states,
 NearCubicWires.LocalBitMultitape.Machine
 (NearCubicWires.P1TopDown.ControllerSelectedContinuation.bodyTapes sources p
  (NearCubicWires.P1TopDown.ControllerCappedRuntime.hierarchyIndex sources p
   (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p))
  (r sources gamma hg hh p) (scratch sources gamma hg hh p)) states)),
∃ (remainingFuel : (open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → Nat → Nat)),
∃ (widths : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → Phase → Nat)),
∃ (phaseConstruction : (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → PCJ2f4bbfb841674a7c_.SelectedConstruction.Inputs sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n) (widths sources gamma hg hh p n x bits))),
∃ (remainingCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (remainingOnset : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (tableCoefficient : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
∃ (tableDegree : ((sources : NearCubicWires.RepairSource.EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : NearCubicWires.RepairSource.CloseoutFinal.Parameters sources gamma) → Nat)),
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.P1TopDown in
∀ (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma),
 let C := ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p);
 ∀ n, remainingOnset sources gamma hg hh p≤n → remainingFuel sources gamma hg hh p n+3≤
 remainingCoefficient sources gamma hg hh p*(n+1)^(remainingDegree sources gamma hg hh p)+
 tableCoefficient sources gamma hg hh p*(2^(SelectedRuntime.width C n-(SelectedRuntime.sigma sources+tableDegree sources gamma hg hh p+2)*
 SelectedRuntime.logarithm C n)*(SelectedRuntime.width C n+1)^(tableDegree sources gamma hg hh p))

noncomputable def buildSelected (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0<den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
   (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
   (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
  (remainingFuel : Nat) (width : Phase → Nat) (supplied : ExpandedSelected sourceBuilder sources p den hden k r scratch n x bits hp site remainingFuel width) :
  PCJ2f4bbfb841674a7c_.SelectedConstruction.Inputs sources p den hden k r scratch n x bits hp site remainingFuel width :=
  Classical.choice (show Nonempty (PCJ2f4bbfb841674a7c_.SelectedConstruction.Inputs sources p den hden k r scratch n x bits hp site remainingFuel width) from by
  dsimp only [ExpandedSelected] at supplied
  rcases supplied with ⟨cost,penaltySpec,momentSpec,clauseSpec,penalty_kept,moment_kept,threshold,head,words,blank,fits⟩
  let penalty := buildPhase sourceBuilder sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .penalty (PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch) (PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp) (cost .penalty) (width .penalty) penaltySpec
  let moment := buildPhase sourceBuilder sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .moment penalty.realize.heads penalty.realize.exit (cost .moment) (width .moment) momentSpec
  let clause := buildPhase sourceBuilder sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) .clause moment.realize.heads moment.realize.exit (cost .clause) (width .clause) clauseSpec
  exact ⟨{cost:=cost,penalty:=penalty,moment:=moment,clause:=clause,penalty_kept:=penalty_kept,moment_kept:=moment_kept,threshold:=threshold,head:=head,words:=words,blank:=blank,fits:=fits}⟩)

/-- Preserve all chosen programs, phase endpoints, widths, fuel and asymptotic fields. -/
theorem construction_of_target (neutral : PCJ1fef9807c6954e94_Native.Target) :
    Construction := by
 classical
 rcases neutral sourceBuilder with
   ⟨capIndex,remainingDegree,r,base,scratch,site,remainingFuel,widths,
    phaseConstruction,remainingCoefficient,remainingOnset,tableCoefficient,tableDegree,runtimeBound⟩
 refine ⟨capIndex,remainingDegree,r,base,scratch,site,remainingFuel,widths,?_,
   remainingCoefficient,remainingOnset,tableCoefficient,tableDegree,runtimeBound⟩
 intro sources gamma hg hh p n x bits C hn hp
 exact buildSelected sources p
   (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p))
   C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp
   (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p n)
   (widths sources gamma hg hh p n x bits)
   (phaseConstruction sources gamma hg hh p n x bits hn hp)

end PCJf08f3457b0ab4c67_Neutral
