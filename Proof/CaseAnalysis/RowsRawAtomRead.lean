import Proof.CaseAnalysis.RowsRawAtomSeek

/-! One original variable block selects and appends its actual cached
polynomial. The index is consumed; only logical cache bytes are scanned.
The existing row copier and marker writer are used without reparsing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRead
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem empty_row_at (C : ℕ) (p : List (List ℕ)) (pre tail out : List Bool) (hc : 1≤C) :
    Step CloseoutRowsRawProductRow.machine (CloseoutRowsRawProductRow.budget [] p)
      (CloseoutRowsRawProductFields.heads 0 pre.length out)
      (CloseoutRowsRawProductFields.data C [false] (pre++ExtIncidence.stream p++tail) out)
      (CloseoutRowsRawProductFields.heads 0 (pre.length+(body p).length) (out++body p))
      (CloseoutRowsRawProductFields.data C [false] (pre++ExtIncidence.stream p++tail) (out++body p)) := by
  obtain ⟨time,ht,tr⟩:=CloseoutRowsRawProductRow.remaining C [] p [] [] pre tail out hc
  have word:CloseoutRowsRawProductRow.word [] p=body p:=by
    simp [CloseoutRowsRawProductRow.word,body]
  simp only [List.flatMap_nil,List.nil_append,List.length_nil,word] at tr
  obtain ⟨r,hr,rf,_⟩:=tr.run (by simp [CloseoutRowsRawProductRow.machine,
    CloseoutRowsRawProductRow.final,RecoveryCalls.machine,RecoveryCalls.stopped])
  have more:=runFrom_moreFuel CloseoutRowsRawProductRow.machine time
    (CloseoutRowsRawProductRow.budget [] p-time) _ r hr
  rw [Nat.add_sub_of_le ht] at more
  exact Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem copy_run (C ip : ℕ) (index pre tail out : List Bool) (p : List (List ℕ)) (hc : 1≤C) :
    Step rightMachine (CloseoutRowsRawProductRow.budget [] p) (heads ip pre.length out)
      (data C index (pre++ExtIncidence.stream p++tail) out)
      (heads ip (pre.length+(body p).length) (out++body p))
      (data C index (pre++ExtIncidence.stream p++tail) (out++body p)) := by
  obtain ⟨raw,hr,rh,rt,_⟩:=empty_row_at C p pre tail out hc
  obtain ⟨r,rr,_rc,_rs,h,t,keep⟩:=RecoveryFocus.dock rightSlots (by decide)
    CloseoutRowsRawProductRow.machine _ (heads ip pre.length out)
    (data C index (pre++ExtIncidence.stream p++tail) out) _
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl) raw hr
  have other:=keep 0 (by intro i;fin_cases i <;> decide)
  refine Step.of_run rr ?_ ?_
  · funext i;fin_cases i
    · exact other.1
    · exact (h 1).trans (congrArg (fun H=>H 1) rh)
    · exact (h 2).trans (congrArg (fun H=>H 2) rh)
    · exact (h 0).trans (congrArg (fun H=>H 0) rh)
    · exact (h 3).trans (congrArg (fun H=>H 3) rh)
  · funext i;fin_cases i
    · exact other.2
    · exact (t 1).trans (congrArg (fun T=>T 1) rt)
    · exact (t 2).trans (congrArg (fun T=>T 2) rt)
    · exact (t 0).trans (congrArg (fun T=>T 0) rt)
    · exact (t 3).trans (congrArg (fun T=>T 3) rt)

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRead
