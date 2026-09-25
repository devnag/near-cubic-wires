import Proof.SourceAssembly.SourceStepsStartHole

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

theorem trace5 (mask : MaskProducer) (selector : CyclicChoice.Laws)
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
    (Hd : Nat → Fin (code ph).sourceTapes → Nat) (Ad : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (siteFuel : Nat) (N : Nat)
    (Inv : Nat → (Fin (code ph).sourceTapes → Nat) → (Fin (code ph).sourceTapes → List Bool) → Prop)
    (seam : SeamSpec N (fun _ => 0) (code ph).slots (inTOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) Inv
      (goodOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)))
    (H0c : Fin (code ph).sourceTapes → Nat) (A0c : Fin (code ph).sourceTapes → List Bool) (h0 : Inv 0 H0c A0c)
    (hN : (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).entries.length ≤ N)
    (hH0 : ∀ i, H0c ((code ph).slots i) = r_inputH (code ph).a ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).ds 0) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).S 0) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).R 0) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).B 0)
      ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).xs 0).length i)
    (hA0 : ∀ i, A0c ((code ph).slots i) = r_inputT (code ph).a ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).ds 0) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).S 0) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).R 0) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).B 0)
      ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).rowWidth 0) (C10PartsSchedule.entryWidthSchedule sources k r n) ((clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve).xs 0).length i)
    (vv : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)
    (hv : vv = chainVals (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve) seam H0c A0c)
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
    
    (hEncH : ∀ j, j ≤ N → ∀ (H : Fin (code ph).sourceTapes → Nat) (A : Fin (code ph).sourceTapes → List Bool), Inv j H A →
      ∀ i, (∀ i', (code ph).slots i' ≠ (code ph).enc i) → H ((code ph).enc i) = 0)
    (hAppH : ∀ j, j ≤ N → ∀ (H : Fin (code ph).sourceTapes → Nat) (A : Fin (code ph).sourceTapes → List Bool), Inv j H A →
      ∀ i, H ((code ph).app i) = 0)
    (hWords : ∀ j, j < N → ∀ (H : Fin (code ph).sourceTapes → Nat) (A : Fin (code ph).sourceTapes → List Bool), Inv j H A →
      (∀ i, (∀ i', (code ph).slots i' ≠ (code ph).enc i) → A ((code ph).enc i) = encInOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve) j i) ∧
      (∀ i, (∀ i', (code ph).slots i' ≠ (code ph).app i) → (∀ i', (code ph).enc i' ≠ (code ph).app i) →
        A ((code ph).app i) = appInOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve) j i))
    -- the code: `app` tapes are never slots; the only `enc` slot is the family's sum slot `5`; `app 0 = enc 6`
    (hAppNS : ∀ i i', (code ph).slots i' ≠ (code ph).app i)
    (hEncS : ∀ i i', (code ph).slots i' = (code ph).enc i → i = 5 ∧ i' = P1TopDownPaidFamilySum.sumSlots (f_raw (code ph).a) 5)
    (hAppE : ∀ i i', (code ph).enc i' = (code ph).app i → i' = 6 ∧ i = 0) (hencInj : Function.Injective (code ph).enc)
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
  have hchain : ∀ j, j ≤ N → Inv j (callChain N (fun _ => 0) (code ph).slots (inTOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) Inv (goodOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) seam H0c A0c j).1 (callChain N (fun _ => 0) (code ph).slots (inTOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) Inv (goodOf (code ph) (C10PartsSchedule.entryWidthSchedule sources k r n) (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve)) seam H0c A0c j).2 := callChain_inv seam H0c A0c h0
  subst hv
  refine traceOfChain mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V
    dflt Dw capw logw resetw old Hd Ad Rc familyCost refillCost firstCost counterReserve H0 A0 siteFuel N Inv seam H0c A0c h0 hN hH0 hA0 _ rfl
    hdeg hC hD hcap hlog h_hw h_hfit h_hold h_hr ?_ ?_ ?_ h_hcost h_hfirst h_hcode hbudget
  · -- E13: the `enc` heads at every call
    dsimp only
    intro j hj i
    by_cases hs : ∃ i', (code ph).slots i' = (code ph).enc i
    · obtain ⟨i', hi'⟩ := hs
      obtain ⟨-, rfl⟩ := hEncS i i' hi'
      rw [← hi', dockH_slot _ (slots_injective (code ph))]
      show dockH (P1TopDownPaidFamilySum.sumSlots (f_raw (code ph).a)) _ (fun _ => 0) _ = 0
      rw [dockH_slot _ (P1TopDownPaidFamilySum.sum_injective _)]
    · have hs' : ∀ i', (code ph).slots i' ≠ (code ph).enc i := fun i' h => hs ⟨i', h⟩
      rw [dockH_other _ _ _ _ hs']
      exact hEncH j (by omega) _ _ (hchain j (by omega)) i hs'
  · -- E13: the `app` heads at every call
    dsimp only
    intro j hj i
    rw [dockH_other _ _ _ _ (hAppNS i)]
    exact hAppH j (by omega) _ _ (hchain j (by omega)) i
  · -- E14: the exact emitter/appender words at every call
    dsimp only
    intro j hj Z _ hsum
    obtain ⟨hwE, hwA⟩ := hWords j (by omega) _ _ (hchain j (by omega))
    refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases hs : ∃ i', (code ph).slots i' = (code ph).enc i
      · obtain ⟨i', hi'⟩ := hs
        obtain ⟨rfl, rfl⟩ := hEncS i i' hi'
        rw [← hi', install_slot _ (slots_injective (code ph))]
        exact hsum
      · have hs' : ∀ i', (code ph).slots i' ≠ (code ph).enc i := fun i' h => hs ⟨i', h⟩
        rw [install_other _ _ _ _ hs']
        exact hwE i hs'
    · by_cases he : ∃ i', (code ph).enc i' = (code ph).app i
      · obtain ⟨i', hi'⟩ := he
        obtain ⟨rfl, rfl⟩ := hAppE i i' hi'
        rw [← hi', install_slot _ hencInj]
        rfl
      · have he' : ∀ i', (code ph).enc i' ≠ (code ph).app i := fun i' h => he ⟨i', h⟩
        rw [install_other _ _ _ _ he', install_other _ _ _ _ (hAppNS i)]
        exact hwA i (hAppNS i) he'

end
end NearCubicWires.SourceSteps
end

