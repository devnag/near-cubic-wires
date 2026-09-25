import Lean
import Proof.Assembly.CappedEntryRuntime
import Proof.Assembly.NeutralConstruction
import Proof.Assembly.SelectedInputs
import Proof.CaseAnalysis.FinalCursorPrologueJoin
import Proof.MachineModel.ClosureActualReusableRow

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native

namespace PCJf08f3457b0ab4c67_Neutral

theorem root_of_construction (construction : Construction) :
    NearCubicWires.RepairSource.EightSources →
      NearCubicWires.RepairSource.OrdinaryHeadlineTheorem25 :=
by
  classical
  obtain ⟨capIndex, remainingDegree, r, base, scratch, site, remainingFuel, widths, phaseConstruction, remainingCoefficient, remainingOnset, tableCoefficient, tableDegree, remainingBound⟩ := construction
  exact (open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown NearCubicWires.P1TopDown.WorkspaceGuardedWorker NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate in
by
  let phaseSequence : open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer NearCubicWires.RepairSource.CloseoutFinal.C10Fusion NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode NearCubicWires.P1TopDown in
(sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → PCJ374c44bb8b7f47d9_.S.SelectedPhases sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp (site sources gamma hg hh p) (pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits)) (NearCubicWires.P1Independent.CappedDecode.proofValueOf sources C.k C.clock p (capIndex sources gamma hg hh p+1) x (oracleOf sources C.k C.clock p.degree n bits) bits) (C10TotalDecode.evaluate (pcpp := pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits))) (remainingFuel sources gamma hg hh p n) (widths sources gamma hg hh p n x bits) := fun sources gamma hg hh p n x bits hn hp =>
    (phaseConstruction sources gamma hg hh p n x bits hn hp).selected
  let ports : (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); Phase → Fin (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).tapes := fun sources gamma hg hh p _n _x _bits =>
    PCJ374c44bb8b7f47d9_.S.ports sources p (ControllerCappedRuntime.hierarchyIndex sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p)) (r sources gamma hg hh p) (scratch sources gamma hg hh p)
  let afterEntry : (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → ∀ ph, PCJ687b3b71abe848ce_.AfterEntry sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) n x bits hp (site sources gamma hg hh p) ph (constantsOf sources) (pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits)) (NearCubicWires.P1Independent.CappedDecode.proofValueOf sources C.k C.clock p (capIndex sources gamma hg hh p+1) x (oracleOf sources C.k C.clock p.degree n bits) bits) (C10TotalDecode.evaluate (pcpp := pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits))) (remainingFuel sources gamma hg hh p n) (ports sources gamma hg hh p n x bits ph) (widths sources gamma hg hh p n x bits ph) := fun sources gamma hg hh p n x bits hn hp ph =>
    (phaseSequence sources gamma hg hh p n x bits hn hp).afterEntry ph
  let physicalTest : (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → let R := fun ph => (afterEntry sources gamma hg hh p n x bits hn hp ph).phaseInput.realizes; readTapeBit ((R .penalty).exit C.result) ((R .penalty).heads C.result) = true ↔ ((((R .penalty).result.value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .penalty ∧ (((R .moment).result.value : Rat) : Real) ≤ C10Verdict.bound (constantsOf sources) .moment ∧ C10Verdict.bound (constantsOf sources) .clause ≤ (((R .clause).result.value : Rat) : Real)) := by
    intro sources gamma hg hh p n x bits C hn hp
    have h := (phaseSequence sources gamma hg hh p n x bits hn hp).physical
    have he := PCJ374c44bb8b7f47d9_.S.flag_eq_result sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p)
    simpa only [he, afterEntry, C, PCJ374c44bb8b7f47d9_.S.SelectedPhases.afterEntry, PCJ687b3b71abe848ce_.AfterEntry.phaseInput, PCJ4bc2e7e825fa4f9c_.PhaseInput.realizes, C10TailComposeVerdict.transport] using h
  let phaseInputs : (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → ∀ ph, PCJ4bc2e7e825fa4f9c_.PhaseInput sources p C.k (r sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) ph (constantsOf sources) (pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits)) (NearCubicWires.P1Independent.CappedDecode.proofValueOf sources C.k C.clock p (capIndex sources gamma hg hh p+1) x (oracleOf sources C.k C.clock p.degree n bits) bits) (C10TotalDecode.evaluate (pcpp := pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits))) (C.fuel n) (fun _ => 0) (let receipt := ControllerCappedSelected.selected_run sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k C.clock C.extra n x bits; WorkspaceSelectedProgram.finalBank receipt.choose receipt.choose_spec.choose C.extra) (ports sources gamma hg hh p n x bits ph) (widths sources gamma hg hh p n x bits ph) := fun sources gamma hg hh p n x bits hn hp ph => (afterEntry sources gamma hg hh p n x bits hn hp ph).phaseInput
  let realizations : (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → (x : BitInput n) → (bits : List Bool) → let C := NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p); (hn : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).onset ≤ n) → (hp : (ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C)).passed n x bits = true) → ∀ ph, Realizes ph (constantsOf sources) (pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits)) (NearCubicWires.P1Independent.CappedDecode.proofValueOf sources C.k C.clock p (capIndex sources gamma hg hh p+1) x (oracleOf sources C.k C.clock p.degree n bits) bits) (C10TotalDecode.evaluate (pcpp := pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits))) C.machine (C.fuel n) (fun _ => 0) (let receipt := ControllerCappedSelected.selected_run sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k C.clock C.extra n x bits; WorkspaceSelectedProgram.finalBank receipt.choose receipt.choose_spec.choose C.extra) (ports sources gamma hg hh p n x bits ph) (widths sources gamma hg hh p n x bits ph) := fun sources gamma hg hh p n x bits hn hp ph => (phaseInputs sources gamma hg hh p n x bits hn hp ph).realizes
  let bodyDegree := fun (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma) => WorkspaceSelectedEntryRuntime.degree sources p (remainingDegree sources gamma hg hh p)
  let coefficient := fun (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma) => PCJ644510ff491048c3_.coefficient sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (remainingCoefficient sources gamma hg hh p)
  let onset := fun (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma) => PCJ644510ff491048c3_.onset sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (remainingOnset sources gamma hg hh p)
  let resourceBounds := fun (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma) => PCJ644510ff491048c3_.bounds sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p) (remainingCoefficient sources gamma hg hh p) (remainingOnset sources gamma hg hh p) (tableCoefficient sources gamma hg hh p) (tableDegree sources gamma hg hh p) (remainingBound sources gamma hg hh p)
  let degreeFit := fun (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma) => (resourceBounds sources gamma hg hh p).1
  let bodyBound := fun (sources : EightSources) (gamma : Real) (hg : 0<gamma) (hh : gamma<1/2) (p : Parameters sources gamma) => (resourceBounds sources gamma hg hh p).2
  let choose := fun sources gamma hg hh p => NearCubicWires.P1TopDown.ControllerCappedRuntime.continuation sources p (capIndex sources gamma hg hh p+1) (remainingDegree sources gamma hg hh p) (r sources gamma hg hh p) (base sources gamma hg hh p) (scratch sources gamma hg hh p) (site sources gamma hg hh p) (remainingFuel sources gamma hg hh p)
  let atoms := fun (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool) =>
    let C := choose sources gamma hg hh p
    (C10TotalDecode.Atom (pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits)))
  let evaluate := fun (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool) =>
    let C := choose sources gamma hg hh p
    (C10TotalDecode.evaluate (pcpp := pcppAt sources C.k C.clock x (oracleOf sources C.k C.clock p.degree n bits)))
  apply ControllerCappedSelected.close
    (fun sources gamma hg hh p => capIndex sources gamma hg hh p+1)
    (fun sources gamma hg hh p => Nat.succ_pos (capIndex sources gamma hg hh p)) choose
  intro sources gamma hg hh p
  apply ControllerCappedRuntime.remaining (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) (choose sources gamma hg hh p) (bodyDegree sources gamma hg hh p) (coefficient sources gamma hg hh p) (onset sources gamma hg hh p) (tableCoefficient sources gamma hg hh p) (tableDegree sources gamma hg hh p) (degreeFit sources gamma hg hh p) (bodyBound sources gamma hg hh p)
  intro n x bits hn hp
  let C := choose sources gamma hg hh p
  let D := ControllerCappedSelected.programData (capIndex sources gamma hg hh p+1) C
  let W := ControllerCappedSelected.workerData sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) D
  let receipt := ControllerCappedSelected.selected_run sources p (capIndex sources gamma hg hh p+1) (Nat.succ_pos (capIndex sources gamma hg hh p)) C.k C.clock C.extra n x bits
  let A0 := WorkspaceSelectedProgram.finalBank receipt.choose receipt.choose_spec.choose C.extra
  let R := realizations sources gamma hg hh p n x bits hn hp
  let H := (R .penalty).heads
  let A := (R .penalty).exit
  have htapes : 2 ≤ W.tapes := by
    change 2 ≤ WorkspaceSelectedAdmission.originalTapes sources p C.k+1+1+C.extra
    omega
  have hpre : Step D.admission (D.preFuel n) (fun _ => 0)
      (entry D.lengthFlag (List.ofFn x) bits) (fun _ => 0) A0 ∧
      readTapeBit (A0 D.admissionFlag) 0 = W.passed n x bits := by
    exact ⟨receipt.choose_spec.choose_spec.1,receipt.choose_spec.choose_spec.2.1⟩
  have hi := inner_pass D.admission D.continuation D.admissionFlag D.result (D.preFuel n) (D.bodyFuel n)
    (fun _ => 0) (fun _ => 0) H (entry D.lengthFlag (List.ofFn x) bits) A0 A
    hpre.1 (hpre.2.trans hp) (R .penalty).run
  have whole := gated_verifier_pass W.onset D.inputTape D.lengthFlag D.result
    (admittedInner D.admission D.continuation D.admissionFlag D.result) htapes rfl
    n x bits hn (D.preFuel n+1+(D.bodyFuel n+1)) H A hi
  have hfuel : ((4*W.onset+1)+1+(D.preFuel n+1+(D.bodyFuel n+1)+1)) = W.fuel n := by
    change ((4*W.onset+1)+1+(D.preFuel n+1+(D.bodyFuel n+1)+1)) =
      4*W.onset+5+D.preFuel n+D.bodyFuel n
    omega
  rw [hfuel] at whole
  have hcut : CloseoutWitness.Soundness.cutoff (constantsOf sources) ≤ W.onset :=
    (Nat.le_max_right C.base _).trans (Nat.le_max_left _ _)
  have gate : LengthGate (constantsOf sources) W.worker htapes W.result W.fuel := by
    have hflag : D.lengthFlag ≠ D.inputTape := by
      intro h
      have hv := congrArg Fin.val h
      change WorkspaceSelectedAdmission.originalTapes sources p C.k+1=0 at hv
      omega
    apply gate_of_rejected_below (constantsOf sources) W.worker htapes W.result W.fuel W.onset hcut
    · change CloseoutWitness.Soundness.cutoff (constantsOf sources) ≤ (4*W.onset+2)+(2+_)
      omega
    · intro n' x' bits' hn'
      obtain ⟨H',A',hr,hfalse⟩ := WorkspaceGuardedWorker.below_run W.onset
        D.admission D.continuation D.inputTape D.lengthFlag D.admissionFlag D.result
        rfl hflag x' bits' hn'
      refine ⟨H',A',?_,hfalse⟩
      rw [UAcceptanceCarrier.inputTapes_eq]
      exact hr.enlarge (by
        change 2*n'+3 ≤ 4*W.onset+5+D.preFuel n'+D.bodyFuel n'
        omega)
  have encoded (ph : Phase) : A (ports sources gamma hg hh p n x bits ph) =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord (widths sources gamma hg hh p n x bits ph) (R ph).result 1 1 := by
    obtain ⟨r,hr,_hh,ht,_hs⟩ := (R .penalty).run
    obtain ⟨r',hr',_hh',ht',_hs'⟩ := (R ph).run
    have he : r=r' := Option.some.inj (hr.symm.trans hr')
    have same := ht.symm.trans ((congrArg (fun z => z.final.tapes) he).trans ht')
    exact (congrFun same _).trans (R ph).hencoded
  refine ⟨atoms sources gamma hg hh p n x bits, evaluate sources gamma hg hh p n x bits,
    ports sources gamma hg hh p n x bits, widths sources gamma hg hh p n x bits, ?_⟩
  exact verdict_of_admitted (constantsOf sources) _ _ (evaluate sources gamma hg hh p n x bits)
    W.worker htapes W.fuel n x bits C.result (ports sources gamma hg hh p n x bits)
    (widths sources gamma hg hh p n x bits) gate (hcut.trans hn) H A whole
    (fun ph => C10TailComposeVerdict.transport (R ph) H A whole (encoded ph))
    (physicalTest sources gamma hg hh p n x bits hn hp)
)

/-- A single semantic supplier construction obligation for the unchanged endpoint. -/
theorem root_of_target (neutral : PCJ1fef9807c6954e94_Native.Target) :
    NearCubicWires.RepairSource.EightSources →
      NearCubicWires.RepairSource.OrdinaryHeadlineTheorem25 :=
  root_of_construction (construction_of_target neutral)

end PCJf08f3457b0ab4c67_Neutral
