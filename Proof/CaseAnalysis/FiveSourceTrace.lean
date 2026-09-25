import Proof.CaseAnalysis.FiveSourceValues

section
/- Source body: PCJ38fbfed565f64139_Source.lean; adapted only for the paid mask load. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace RCFive.Source
open PCJc4297ab269d8423a_Source
attribute [local irreducible] P1TopDownPaidPayload.tapes

/- Execution and semantic facts about those exact values and machines. -/
structure SourceTrace  (mask : MaskProducer) (selector : CyclicChoice.Laws) (packets : PacketLibrary selector) (rows : RowLibrary selector) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat)
 (code : SourceCode mask selector packets rows sources p k r scratch ph)
 (values : SourceValues mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code) : Prop where
  _horder :
    let order := values.order
    let pcpp := pcppAt sources k clock x oracle
    let coordinate := PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits
    order.Perm (CloseoutFinalC10SupplierCalls.siteCalls ph pcpp coordinate C10TotalDecode.Atom.systematic ci).monomials
  _hlen :
    let order := values.order
    let entries := values.entries
    entries.length=order.length
  _hxs :
    let ds := values.ds
    let xs := values.xs
    xs=fun j=>(ds j).map PCJ9eff70d512234a4c_Fixed.datumValue
  _hcoeff :
    let order := values.order
    let coefficient := values.coefficient
    let entries := values.entries
    ∀ j<entries.length,coefficient j=CloseoutFinalC10SupplierCalls.coefficientEstimate
      ((order.map (fun m=>m.coefficient)).getD j 0)
  _hnative :
    let a := code.a
    let order := values.order
    let L := values.L
    let target := values.target
    let ds := values.ds
    let S := values.S
    let R := values.R
    let B := values.B
    let rowWidth := values.rowWidth
    let total := values.total
    let denominator := values.denominator
    let entries := values.entries
    ∀ j<entries.length,NativeRows selector compiler sources L target mode
      ((order.map (fun m=>m.factors)).getD j []) a (S j) (R j) (B j) (rowWidth j) (ds j) (total j) (denominator j)
  _hw :
    let rowWidth := values.rowWidth
    let entries := values.entries
    ∀ j<entries.length,rowWidth j≤b
  _hfit :
    let total := values.total
    let entries := values.entries
    ∀ j<entries.length,total j<2^b
  _hH :
    let a := code.a
    let slots := code.slots
    let ds := values.ds
    let xs := values.xs
    let S := values.S
    let R := values.R
    let B := values.B
    let entries := values.entries
    let H := values.H
    ∀ j<entries.length,∀ i,H j (slots i)=r_inputH a (ds j) (S j) (R j) (B j) (xs j).length i
  _hA :
    let a := code.a
    let slots := code.slots
    let ds := values.ds
    let xs := values.xs
    let S := values.S
    let R := values.R
    let B := values.B
    let rowWidth := values.rowWidth
    let entries := values.entries
    let A := values.A
    ∀ j<entries.length,∀ i,A j (slots i)=r_inputT a (ds j) (S j) (R j) (B j)
       (rowWidth j) b (xs j).length i
  _hc :
    let cap := values.cap
    let entries := values.entries
    ∀ j<entries.length,4*b+5≤cap j
  _hold :
    let D := values.D
    let old := values.old
    let entries := values.entries
    ∀ j<entries.length,(old j).length≤D j
  _hl :
    let logSize := values.logSize
    let entries := values.entries
    ∀ j<entries.length,20*b+27≤logSize j
  _hr :
    let resetSize := values.resetSize
    let phasePrefix := values.phasePrefix
    let entries := values.entries
    ∀ j<entries.length,CloseoutFinalC10AppendPositioning.rawBudget b (phasePrefix++entries.take j).length≤resetSize j
  _heH :
    let a := code.a
    let slots := code.slots
    let enc := code.enc
    let ds := values.ds
    let xs := values.xs
    let S := values.S
    let R := values.R
    let B := values.B
    let rowWidth := values.rowWidth
    let entries := values.entries
    let H := values.H
    ∀ j<entries.length,∀ i,dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j)) (enc i)=0
  _haH :
    let a := code.a
    let slots := code.slots
    let app := code.app
    let ds := values.ds
    let xs := values.xs
    let S := values.S
    let R := values.R
    let B := values.B
    let rowWidth := values.rowWidth
    let entries := values.entries
    let H := values.H
    ∀ j<entries.length,∀ i,dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j)) (app i)=0
  _hfields :
    let a := code.a
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let ds := values.ds
    let xs := values.xs
    let S := values.S
    let R := values.R
    let B := values.B
    let rowWidth := values.rowWidth
    let total := values.total
    let denominator := values.denominator
    let D := values.D
    let cap := values.cap
    let logSize := values.logSize
    let resetSize := values.resetSize
    let coefficient := values.coefficient
    let old := values.old
    let phasePrefix := values.phasePrefix
    let entries := values.entries
    let A := values.A
    ∀ j<entries.length,∀ Z,
       Step (f_machine a) (f_budget a (S j) (rowWidth j) b (xs j).length)
        (r_inputH a (ds j) (S j) (R j) (B j) (xs j).length)
        (r_inputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j).length)
        (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
        (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z)  → 
       r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z
        (P1TopDownPaidFamilySum.sumSlots (f_raw a) 5)=RepairOrdinary.frame (SignedSortKey.binary b (total j))  → 
       let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
       let mid := install slots (A j)
        (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z)
       (∀ i,mid (enc i)=e_bank b entry (D j) (cap j) (old j) i) ∧
       (∀ i,install enc mid (e_bank b entry (D j) (cap j)
         (ZeroPadding.pad (D j) (Stream.entryWord b entry))) (app i)=
         CloseoutFinalC10AppendPositioning.tapes b (D j) (logSize j) (resetSize j) entry (phasePrefix++entries.take j) i)
  _hcost :
    let a := code.a
    let xs := values.xs
    let S := values.S
    let rowWidth := values.rowWidth
    let D := values.D
    let phasePrefix := values.phasePrefix
    let entries := values.entries
    let familyCost := values.familyCost
    let fuel := fun j=>f_budget a (S j) (rowWidth j) b (xs j).length+1+
       (2*D j+4+1+(2*e_emitCost b+2)+1+
        CloseoutFinalC10AppendPositioning.budget b (phasePrefix++entries.take j).length)
    (∀ j<entries.length,fuel j≤familyCost)
  _hrefill :
    let a := code.a
    let sourceTapes := code.sourceTapes
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let refillCode := code.refillCode
    let ds := values.ds
    let xs := values.xs
    let S := values.S
    let R := values.R
    let B := values.B
    let rowWidth := values.rowWidth
    let total := values.total
    let denominator := values.denominator
    let D := values.D
    let cap := values.cap
    let logSize := values.logSize
    let resetSize := values.resetSize
    let coefficient := values.coefficient
    let phasePrefix := values.phasePrefix
    let entries := values.entries
    let H := values.H
    let A := values.A
    let reserveSize := values.reserveSize
    let refillCost := values.refillCost
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let fuel := fun j=>f_budget a (S j) (rowWidth j) b (xs j).length+1+
       (2*D j+4+1+(2*e_emitCost b+2)+1+
        CloseoutFinalC10AppendPositioning.budget b (phasePrefix++entries.take j).length)
    let outH := fun j=>dockH slots (H j)
       (r_outputH a (ds j) (S j) (R j) (B j) (rowWidth j) (xs j))
    let outA := fun j Z=>
       let entry : Stream.Entry := ⟨coefficient j,total j,denominator j⟩
       install app
        (install enc (install slots (A j)
          (r_outputT a (ds j) (S j) (R j) (B j) (rowWidth j) b (xs j) Z))
         (e_bank b entry (D j) (cap j) (ZeroPadding.pad (D j) (Stream.entryWord b entry))))
        (CloseoutFinalC10AppendPositioning.tapes b (D j) (logSize j) (resetSize j)
          entry ((phasePrefix++entries.take j)++[entry]))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    (∀ j<entries.length,∀ Z,Step family (fuel j) (H j) (A j) (outH j) (outA j Z)  → 
       MaskFamilyCode.Prepared refillCode (ds (j+1)) refillCost
        (outH j) (H (j+1)) (fun i=>ZeroPadding.pad (reserve i) (outA j Z i)) (padded (j+1)))
  _hfirst :
    let a := code.a
    let sourceTapes := code.sourceTapes
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let refillCode := code.refillCode
    let firstCode := code.firstCode
    let whole := code.whole
    let ds := values.ds
    let entries := values.entries
    let H := values.H
    let A := values.A
    let reserveSize := values.reserveSize
    let firstCost := values.firstCost
    let counterReserve := values.counterReserve
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) globalA
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ci).right]))
    let originalH := fun i=>globalH (whole i)
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
       (fun i=>ZeroPadding.pad (counterCaps i) ((RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes i))
  _hfinalH :
    let a := code.a
    let sourceTapes := code.sourceTapes
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let refillCode := code.refillCode
    let whole := code.whole
    let entries := values.entries
    let H := values.H
    let A := values.A
    let reserveSize := values.reserveSize
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    (dockH whole globalH (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).heads=globalHnext)
  _hfinalA :
    let a := code.a
    let sourceTapes := code.sourceTapes
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let refillCode := code.refillCode
    let whole := code.whole
    let entries := values.entries
    let H := values.H
    let A := values.A
    let reserveSize := values.reserveSize
    let counterReserve := values.counterReserve
    let refillCycle := refillCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let reserve := fun (i : Fin sourceTapes) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
    let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode) globalA
       (PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle) ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle))) (req sources k clock x oracle).arity ci.val
         (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources) ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity))
         (natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ci).left,
           literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauses ci).right]))
    let counterCaps : Fin (sourceTapes+1) → Nat := fun i=>if i.val=sourceTapes then counterReserve else 0
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let padded := fun j i=>ZeroPadding.pad (reserve i) (A j i)
    let body := Composition.machine family refill
    let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration sourceTapes _)
    (install whole queried (fun i=>ZeroPadding.pad (counterCaps i)
        ((RepeatMachine.cfg 3 (state entries.length []) entries.length 1).tapes i))=globalAfter)
  _hcode :
    let a := code.a
    let slots := code.slots
    let enc := code.enc
    let app := code.app
    let refillCode := code.refillCode
    let firstCode := code.firstCode
    let whole := code.whole
    let refillCycle := refillCode.base.cached
    let firstCycle := firstCode.base.cached
    let refill := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code refillCycle)
    let first := PCJ38fbfed565f64139_Cycle.machine (PCJ38fbfed565f64139_Cached.code firstCycle)
    let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
      (Composition.machine (RecoveryFocus.machine enc e_machine)
        (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
    let body := Composition.machine family refill
    (⟨_,RecoveryFocus.machine whole (Composition.machine first (CloseoutRowsDegreeLoop.machine body))⟩ : Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)=site mode ph
  budget :
    let entries := values.entries
    let familyCost := values.familyCost
    let refillCost := values.refillCost
    let firstCost := values.firstCost
    firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3) ≤ siteFuel

theorem SourceTrace.toSpec  (mask : MaskProducer) (selector : CyclicChoice.Laws) (packets : PacketLibrary selector) (rows : RowLibrary selector) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat)
 (code : SourceCode mask selector packets rows sources p k r scratch ph)
 (values : SourceValues mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code)
 (trace : SourceTrace mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel code values) :
 MaskedSourceSpec mask selector packets rows compiler sources p k den r scratch clock n x oracle bits site mode ph ci globalH globalHnext globalA globalAfter b siteFuel := by
  rcases code with ⟨a,prepT,_hsize,sourceTapes,slots,_hs,enc,_he,app,_ha,refillCode,firstCode,_refillSource,_firstSource,whole,_hwhole⟩
  rcases values with ⟨order,L,target,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,H,A,reserveSize,familyCost,refillCost,firstCost,counterReserve⟩
  rcases trace with ⟨_horder,_hlen,_hxs,_hcoeff,_hnative,_hw,_hfit,_hH,_hA,_hc,_hold,_hl,_hr,_heH,_haH,_hfields,_hcost,_hrefill,_hfirst,_hfinalH,_hfinalA,_hcode,budget⟩
  exact ⟨order,_horder,L,target,a,prepT,_hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,_hlen,_hxs,_hcoeff,_hnative,sourceTapes,slots,_hs,enc,_he,app,_ha,H,A,reserveSize,_hw,_hfit,_hH,_hA,_hc,_hold,_hl,_hr,_heH,_haH,_hfields,familyCost,refillCost,firstCost,refillCode,firstCode,_refillSource,_firstSource,whole,_hwhole,counterReserve,_hcost,_hrefill,_hfirst,_hfinalH,_hfinalA,_hcode,budget⟩

end RCFive.Source
end
