import Proof.Assembly.NativeSelected
import Proof.Assembly.FamilyRecord

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native

namespace PCJf08f3457b0ab4c67_Neutral

/-- Actual source execution for arbitrary valid descriptors; no canonical row premise. -/
theorem sourceBuilder : PCJ1fef9807c6954e94_Native.SourceBuilder := by
 classical
 intro sources gamma p k r scratch site mode ph pcpp_a rq ci globalH globalHnext
   globalA globalAfter b siteFuel supplied
 rcases supplied with ⟨a,prepT,hsize,dflt,ds,xs,S,R,B,rowWidth,total,denominator,D,cap,logSize,resetSize,coefficient,old,phasePrefix,entries,U,slots,hs,enc,he,app,ha,H,A,reserveSize,hv,hwords,hw,hx,hsum,hfit,hH,hA,hc,hold,hl,hr,heH,haH,hfields,familyCost,refillCost,firstCost,refillStates,firstStates,refill,first,whole,hwhole,counterReserve,hcost,hrefill,hfirst,hfinalH,hfinalA,hcode,hbound⟩
 subst scratch
 have physical :
  let reserve := fun (i : Fin U) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
   let queried := install (PCJda54a286946142d3_BranchPhases.cache sources p k r (r_tapes a+14+prepT) mode) globalA
     (PCPPQueryIndexPadding.clauseData (pcppOutput rq (pcpp_a.output rq)) rq.arity ci.val
       (PCPPQueryCachedBounds.capacity pcpp_a (rq.circuit.size+rq.arity))
       (natListWord [literalIndex ((pcpp_a.output rq).clauses ci).left,
         literalIndex ((pcpp_a.output rq).clauses ci).right]))
   let originalH := fun i=>globalH (whole i)
   let originalA := fun i=>queried (whole i)
   let counterCaps : Fin (U+1) → Nat := fun i=>if i.val=U then counterReserve else 0
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
   let body := Composition.machine family refill
   let state := fun j (_out : List Bool)=>(⟨body.start,H j,padded j⟩ : Configuration U _)
  Step (RecoveryFocus.machine whole (Composition.machine first (CloseoutRowsDegreeLoop.machine body)))
    (firstCost+1+(entries.length*(familyCost+1+refillCost+3)+3)) globalH queried globalHnext globalAfter
 := by
   dsimp only
   let reserve := fun (i : Fin U) => if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then reserveSize else 0
   have si : Function.Injective slots := by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    rw [hs,hs] at hh
    omega
   have hT : 6≤r_tapes a := Nat.le_trans (by decide : 6≤11) (Nat.le_add_left 11 _)
   have ei : Function.Injective enc := by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    rw [he,he] at hh
    have hi := i.isLt; have hj := j.isLt
    split_ifs at hh <;> omega
   have hpublic : (CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r (r_tapes a+14+prepT)) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (r_tapes a+14+prepT)) ph 81).val<(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155 ∧ (CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r (r_tapes a+14+prepT)) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (r_tapes a+14+prepT)) ph 90).val<(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155 ∧ (CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r (r_tapes a+14+prepT)) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (r_tapes a+14+prepT)) ph 81).val≠(CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r) (ControllerSelectedContinuation.bodyTapes sources p k r (r_tapes a+14+prepT)) (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r) (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (r_tapes a+14+prepT)) ph 90).val := by
    cases ph <;> norm_num [CloseoutFinalC10RetainedPhaseFold.wordSlots,
     CloseoutFinalC10RetainedPhaseFold.phaseBank,C10TailUniformSlots.phaseIndex]
   have ai : Function.Injective app := by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    simp only [ha] at hh
    fin_cases i <;> fin_cases j <;> norm_num at hh <;> omega
   have wi : Function.Injective whole := by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    simpa only [hwhole] using hh
   let family := Composition.machine (RecoveryFocus.machine slots (f_machine a))
    (Composition.machine (RecoveryFocus.machine enc e_machine)
      (RecoveryFocus.machine app CloseoutFinalC10SingleAppend.machine))
   let body := Composition.machine family refill
   let state := fun j (_out : List Bool)=>(⟨body.start,H j,fun i=>ZeroPadding.pad (reserve i) (A j i)⟩ : Configuration U _)
   have iteration : ∀ j<entries.length,∀ out,∃ r,
     runFrom body (familyCost+1+refillCost) (state j out)=some r ∧
     r.final.heads=(state (j+1) (out++[])).heads ∧
     r.final.tapes=(state (j+1) (out++[])).tapes ∧ r.steps≤familyCost+1+refillCost := by
    intro j hj out
    obtain ⟨Z,hfamily⟩ := PCJ9856d3e73b1d4df0_.FamilyRecord.run a (ds j) (S j) (R j) (B j) (rowWidth j) b
     (xs j) (total j) dflt (hv j hj) (hwords j hj) (hw j hj) (hx j hj) (hsum j hj) (hfit j hj)
     slots si enc ei app ai (coefficient j) (denominator j) (D j) (cap j) (logSize j) (resetSize j)
     (old j) (phasePrefix++entries.take j) (H j) (A j) (hH j hj) (hA j hj) (hc j hj) (hold j hj)
     (hl j hj) (hr j hj) (heH j hj) (haH j hj) (hfields j hj)
    have joined := (hfamily.pad reserve).seq (hrefill j hj Z hfamily)
    exact joined.enlarge (Nat.add_le_add_right (Nat.add_le_add_right (hcost j hj) 1) refillCost)
   obtain ⟨runResult,rr,rf,rs⟩ := CloseoutRowsDegreeLoop.loop_run body state (fun _=>[])
     (familyCost+1+refillCost) entries.length (by intros; rfl) iteration []
   have hloop : Step (CloseoutRowsDegreeLoop.machine body) (entries.length*(familyCost+1+refillCost+3)+3)
     (RepeatMachine.cfg 0 (state 0 []) entries.length 1).heads (RepeatMachine.cfg 0 (state 0 []) entries.length 1).tapes
     (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).heads (RepeatMachine.cfg 3 (state entries.length []) entries.length 1).tapes := by
    refine ⟨runResult,rr,?_,?_,rs⟩
    · rw [rf]
    · rw [rf]
   have joined := hfirst.seq (hloop.pad (fun i=>if i.val=U then counterReserve else 0))
   have docked := joined.dock whole wi globalH
     (install (PCJda54a286946142d3_BranchPhases.cache sources p k r (r_tapes a+14+prepT) mode) globalA
      (PCPPQueryIndexPadding.clauseData (pcppOutput rq (pcpp_a.output rq)) rq.arity ci.val
        (PCPPQueryCachedBounds.capacity pcpp_a (rq.circuit.size+rq.arity))
        (natListWord [literalIndex ((pcpp_a.output rq).clauses ci).left,
          literalIndex ((pcpp_a.output rq).clauses ci).right])))
     (fun _=>rfl) (fun _=>rfl)
   exact docked.congr hfinalH hfinalA
 rw [←hcode]
 exact physical.enlarge hbound

end PCJf08f3457b0ab4c67_Neutral
