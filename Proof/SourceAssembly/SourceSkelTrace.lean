import Proof.SourceAssembly.SourceSkelClause

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- **`SourceTrace` from its per-call machine content**, at the chosen values `vv = clauseVals …`. -/
theorem traceOf (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat) (old : Nat → List Bool)
    (Hc : Nat → Fin (code ph).sourceTapes → Nat) (Ac : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (siteFuel : Nat)
    (vv : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)
    (hv : vv = clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hc Ac Rc familyCost refillCost
      firstCost counterReserve)
    (hdeg : ∀ j, j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length →
      min (lay j).degree (Packets.pool (decompositionOf sources)
        (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))
        (Packets.geometry selector
          (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j)))).length = deg j)
    (hC : ∀ j, j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length →
      RCFive.NativeResources.streamCap (decompositionOf sources)
        (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))
        (Packets.geometry selector
          (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))) (lay j)
        ≤ (lay j).C)
    (hD : ∀ j, j < (TraceData.order (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci).length →
      RCFive.NativeResources.driverCap (decompositionOf sources)
        (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))
        (Packets.geometry selector
          (Packets.request sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) (SourceRequest.FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci j))) (lay j)
          (code ph).a ≤ V)
    (hcap : 4*(C10PartsSchedule.entryWidthSchedule sources k r n)+5 ≤ capw) (hlog : 20*(C10PartsSchedule.entryWidthSchedule sources k r n)+27 ≤ logw)
    (h_hw :
    let rowWidth := vv.rowWidth
    let entries := vv.entries
    ∀ j<entries.length,rowWidth j≤(C10PartsSchedule.entryWidthSchedule sources k r n))
    (h_hfit :
    let total := vv.total
    let entries := vv.entries
    ∀ j<entries.length,total j<2^(C10PartsSchedule.entryWidthSchedule sources k r n))
    (h_hH :
    let a := (code ph).a
    let slots := (code ph).slots
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let entries := vv.entries
    let H := vv.H
    ∀ j<entries.length,∀ i,H j (slots i)=r_inputH a (ds j) (S j) (R j) (B j) (xs j).length i)
    (h_hA :
    let a := (code ph).a
    let slots := (code ph).slots
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let entries := vv.entries
    let A := vv.A
    ∀ j<entries.length,∀ i,A j (slots i)=r_inputT a (ds j) (S j) (R j) (B j)
       (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j).length i)
    (h_hold :
    let D := vv.D
    let old := vv.old
    let entries := vv.entries
    ∀ j<entries.length,(old j).length≤D j)
    (h_hr :
    let resetSize := vv.resetSize
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    ∀ j<entries.length,CloseoutFinalC10AppendPositioning.rawBudget (C10PartsSchedule.entryWidthSchedule sources k r n) (phasePrefix++entries.take j).length≤resetSize j)
    (h_heH :
    let a := (code ph).a
    let slots := (code ph).slots
    let enc := (code ph).enc
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let entries := vv.entries
    let H := vv.H
    ∀ j<entries.length,∀ i,dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j)) (enc i)=0)
    (h_haH :
    let a := (code ph).a
    let slots := (code ph).slots
    let app := (code ph).app
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let entries := vv.entries
    let H := vv.H
    ∀ j<entries.length,∀ i,dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j)) (app i)=0)
    (h_hfields :
    let a := (code ph).a
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let total := vv.total
    let denominator := vv.denominator
    let D := vv.D
    let cap := vv.cap
    let logSize := vv.logSize
    let resetSize := vv.resetSize
    let coefficient := vv.coefficient
    let old := vv.old
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    let A := vv.A
    ∀ j<entries.length,∀ Z,
       Step (f_machine a) (f_budget a (S j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j).length)
        (r_inputH a (ds j) (S j) (R j) (B j) (xs j).length)
        (r_inputT a (ds j) (S j) (R j) (B j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j).length)
        (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
        (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j) Z)  → 
       r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j) Z
        (P1TopDownPaidFamilySum.sumSlots (f_raw a) 5)=RepairOrdinary.frame (SignedSortKey.binary (C10PartsSchedule.entryWidthSchedule sources k r n) (total j))  → 
       let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
       let mid := install slots (A j)
        (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j) Z)
       (∀ i,mid (enc i)=e_bank (C10PartsSchedule.entryWidthSchedule sources k r n) entry (D j) (cap j) (old j) i) ∧
       (∀ i,install enc mid (e_bank (C10PartsSchedule.entryWidthSchedule sources k r n) entry (D j) (cap j)
         (ZeroPadding.pad (D j) (Stream.entryWord (C10PartsSchedule.entryWidthSchedule sources k r n) entry))) (app i)=
         CloseoutFinalC10AppendPositioning.tapes (C10PartsSchedule.entryWidthSchedule sources k r n) (D j) (logSize j) (resetSize j) entry (phasePrefix++entries.take j) i))
    (h_hcost :
    let a := (code ph).a
    let xs := vv.xs
    let S := vv.S
    let rowWidth := vv.rowWidth
    let D := vv.D
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    let familyCost := vv.familyCost
    let fuel := fun j=>f_budget a (S j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j).length+1+
       (2*D j+4+1+(2*e_emitCost (C10PartsSchedule.entryWidthSchedule sources k r n)+2)+1+
        CloseoutFinalC10AppendPositioning.budget (C10PartsSchedule.entryWidthSchedule sources k r n) (phasePrefix++entries.take j).length)
    (∀ j<entries.length,fuel j≤familyCost))
    (h_hrefill :
    let a := (code ph).a
    let sourceTapes := (code ph).sourceTapes
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let ds := vv.ds
    let xs := vv.xs
    let S := vv.S
    let R := vv.R
    let B := vv.B
    let rowWidth := vv.rowWidth
    let total := vv.total
    let denominator := vv.denominator
    let D := vv.D
    let cap := vv.cap
    let logSize := vv.logSize
    let resetSize := vv.resetSize
    let coefficient := vv.coefficient
    let phasePrefix := vv.phasePrefix
    let entries := vv.entries
    let H := vv.H
    let A := vv.A
    let reserveSize := vv.reserveSize
    let refillCost := vv.refillCost
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let fuel := fun j=>f_budget a (S j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j).length+1+
       (2*D j+4+1+(2*e_emitCost (C10PartsSchedule.entryWidthSchedule sources k r n)+2)+1+
        CloseoutFinalC10AppendPositioning.budget (C10PartsSchedule.entryWidthSchedule sources k r n) (phasePrefix++entries.take j).length)
    let outH := fun j=>dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
    let outA := fun j Z=>
       let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
       install app
        (install enc (install slots (A j)
          (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) (C10PartsSchedule.entryWidthSchedule sources k r n) (xs j) Z))
         (e_bank (C10PartsSchedule.entryWidthSchedule sources k r n) entry (D j) (cap j) (ZeroPadding.pad (D j) (Stream.entryWord (C10PartsSchedule.entryWidthSchedule sources k r n) entry))))
        (CloseoutFinalC10AppendPositioning.tapes (C10PartsSchedule.entryWidthSchedule sources k r n) (D j) (logSize j) (resetSize j)
          entry ((phasePrefix++entries.take j)++[entry]))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    (∀ j<entries.length,∀ Z,Step family (fuel j) (H j) (A j) (outH j) (outA j Z)  → 
       MaskFamilyCode.Prepared refillCode (ds (j+1)) refillCost
        (outH j) (H (j+1)) (fun i=>ZeroPadding.pad (reserve i) (outA j Z i)) (padded (j+1))))
    (h_hfirst :
    let a := (code ph).a
    let sourceTapes := (code ph).sourceTapes
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let firstCode := (code ph).firstCode
    let whole := (code ph).whole
    let ds := vv.ds
    let entries := vv.entries
    let H := vv.H
    let A := vv.A
    let reserveSize := vv.reserveSize
    let firstCost := vv.firstCost
    let counterReserve := vv.counterReserve
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) A0
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))) (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ci).right]))
    let originalH := fun i=>H0 (whole i)
    let originalA := fun i=>queried (whole i)
    let counterCaps : Fin (sourceTapes+1) → Nat := fun i=>if i.val=sourceTapes then counterReserve else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    MaskFamilyCode.Prepared firstCode (ds 0) firstCost originalH
       (RepeatMachine.cfg 0 (state 0 []) entries.length 1).heads originalA
       (fun i=>ZeroPadding.pad (counterCaps i) ((RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes i)))
    (h_hcode :
    let a := (code ph).a
    let slots := (code ph).slots
    let enc := (code ph).enc
    let app := (code ph).app
    let refillCode := (code ph).refillCode
    let firstCode := (code ph).firstCode
    let whole := (code ph).whole
    let refillCycle := refillCode.base.cached
    let firstCycle := firstCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let first := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code firstCycle)
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let body := Composition.machine family refill
    (⟨_,RecoveryFocus.machine whole (Composition.machine first (CloseoutRowsDegreeLoop.machine body))⟩ : Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)=site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph)
    (hbudget :
    let entries := vv.entries
    let familyCost := vv.familyCost
    let refillCost := vv.refillCost
    let firstCost := vv.firstCost
    firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3) ≤ siteFuel) :
    RCFive.Source.SourceTrace mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
      site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph ci H0 (finalH mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 vv) A0 (finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 vv) (C10PartsSchedule.entryWidthSchedule sources k r n) siteFuel (code ph) vv := by
  subst hv
  exact
    { _horder := List.Perm.refl _
      _hlen := TraceData.hlen (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)
      _hxs := rfl
      _hcoeff := fun _ _ => rfl
      _hnative := TraceData.hnative (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector compiler (code ph).a lay V deg hdeg hC hD
      _hw := h_hw
      _hfit := h_hfit
      _hH := h_hH
      _hA := h_hA
      _hc := fun _ _ => hcap
      _hold := h_hold
      _hl := fun _ _ => hlog
      _hr := h_hr
      _heH := h_heH
      _haH := h_haH
      _hfields := h_hfields
      _hcost := h_hcost
      _hrefill := h_hrefill
      _hfirst := h_hfirst
      _hfinalH := rfl
      _hfinalA := rfl
      _hcode := h_hcode
      budget := hbudget }

end
end NearCubicWires.SourceSkeleton
end
