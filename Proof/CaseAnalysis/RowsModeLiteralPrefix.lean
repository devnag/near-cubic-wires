import Proof.CaseAnalysis.RowsModeLiteralMarks

/-! The original cell flag physically emits the constant member of a
literal pair; its variable member is emitted by the retained index copier. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPrefix
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsModeLiteralMarks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 5 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then
    if bits 4 then some ⟨1,fun i=>if i=2 then some true else none,fun i=>if i=2 then .right else .stay⟩
    else some ⟨2,fun _=>none,fun _=>.stay⟩
    else if q=1 then some ⟨2,fun i=>if i=2 then some false else none,fun i=>if i=2 then .right else .stay⟩
    else none
def constant (neg : Bool) : List Bool:=if neg then [true,false] else []

theorem start_step (neg : Bool) (source out : List Bool) (pos j count : Nat) :
    step machine (cfg 0 source pos j count out neg)=
      some (cfg (if neg then 1 else 2) source pos j count (out++emitted neg true) neg):=by
  have hf:(cfg (0 : Fin 3) source pos j count out neg).scanned 4=neg:=rfl
  simp only [step,machine,hf]
  cases neg <;> apply congrArg some <;> apply configuration_ext
  all_goals first
    | rfl
    | (funext i;fin_cases i <;>
        simp [applyAction,cfg,heads,data,emitted,Fin.addCases,RowMaskBodyParts.cfg,HeadMove.apply,Streaming.write_append])

theorem finish_step (source out : List Bool) (pos j count : Nat) :
    step machine (cfg 1 source pos j count out true)=
      some (cfg 2 source pos j count (out++[false]) true):=by
  simp only [step,machine]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>
      simp [applyAction,cfg,heads,Fin.addCases,RowMaskBodyParts.cfg,HeadMove.apply]
  · funext i;fin_cases i <;>
      simp [applyAction,cfg,heads,data,Fin.addCases,RowMaskBodyParts.cfg,Streaming.write_append]

theorem prefix_run (neg : Bool) (source out : List Bool) (pos j count : Nat) :
    Step machine 2 (heads pos j count out) (data source j count out neg)
      (heads pos j count (out++constant neg)) (data source j count (out++constant neg) neg):=by
  cases neg
  · obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) (start_step false source out pos j count)).run (by rfl)
    have raw:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
    simpa only [constant,emitted,Bool.false_eq_true,if_false,List.append_nil,cfg] using raw.enlarge (by omega)
  · have raw:=(Timed.single (by rfl) (start_step true source out pos j count)).trans
      (Timed.single (by rfl) (finish_step source (out++[true]) pos j count))
    obtain ⟨r,hr,rf,_⟩:=raw.run (by rfl)
    simpa only [constant,if_true,List.append_assoc,List.cons_append,List.nil_append,cfg] using
      Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPrefix
