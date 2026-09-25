import Proof.CaseAnalysis.RowsModeTupleLoop

/-! One actual enumerated tuple frame emits exactly one raw monomial,
including its two monomial markers and the paid three-cell source trailer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : Nat) (out : List Bool) : Fin 7→Nat:=![pos,0,1,0,0,out.length,1]
def data (w k C : Nat) (source copy out : List Bool) : Fin 7→List Bool:=
  ![source,frame copy,CompareMachine.word w,[false],List.replicate C false,out,CompareMachine.word k]
def loopBudget (w k M : Nat):=k*(CloseoutRowsModeTupleDigit.budget w M+3)+3

theorem loop_run (w C M : Nat) (ds : List Nat) (pre tail copy out : List Bool)
    (hc : 2*w+1≤C) (hcopy : copy.length≤w)
    (hd : ∀ d∈ds,d<2^w) (hM : ∀ d∈ds,d≤M) :
    ∃ residue : List Bool,residue.length≤w ∧
      Step CloseoutRowsModeTupleLoop.machine (loopBudget w ds.length M) (heads pre.length out)
        (data w ds.length C (pre++RowTupleFilterLoop.word w ds++tail) copy out)
        (heads (pre.length+(RowTupleFilterLoop.word w ds).length) (out++ds.flatMap ExtIncidence.block))
        (data w ds.length C (pre++RowTupleFilterLoop.word w ds++tail) residue (out++ds.flatMap ExtIncidence.block)) := by
  obtain ⟨residue,hres,time,ht,trace⟩:=CloseoutRowsModeTupleLoop.remaining w ds.length C M 0 ds
    pre tail copy out (by omega) hc hcopy hd hM
  have hb:time≤loopBudget w ds.length M:=by unfold loopBudget;nlinarith
  obtain ⟨r,hr,rf,_⟩:=trace.run (by simp [CloseoutRowsModeTupleLoop.machine,CloseoutRowsModeTupleLoop.cfg,
    RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more:=runFrom_moreFuel CloseoutRowsModeTupleLoop.machine time (loopBudget w ds.length M-time) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  have raw:=Step.of_run more (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  refine ⟨residue,hres,(raw.congr_in ?_ ?_).congr ?_ ?_⟩
  all_goals funext i;fin_cases i <;> rfl

def first : Machine 7 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun i=>if i=5 then some true else none,
    fun i=>if i=5 then .right else .stay⟩ else none
def last : Machine 7 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q _=>if h:q.val<3 then some ⟨⟨q.val+1,by omega⟩,
    fun i=>if q=0 ∧ i=5 then some false else none,
    fun i=>if i=0 ∨ (q=0 ∧ i=5) then .right else .stay⟩ else none
noncomputable def machine:=Composition.machine (Composition.machine first CloseoutRowsModeTupleLoop.machine) last
def budget (w k M : Nat):=loopBudget w k M+6

theorem first_run (w k C pos : Nat) (source copy out : List Bool) :
    Step first 1 (heads pos out) (data w k C source copy out)
      (heads pos (out++[true])) (data w k C source copy (out++[true])) := by
  have h:step first ⟨0,heads pos out,data w k C source copy out⟩=
      some ⟨1,heads pos (out++[true]),data w k C source copy (out++[true])⟩:=by
    simp [step,first]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,heads,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,heads,data,Streaming.write_append]
  obtain ⟨r,hr,rf,_⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem last_run (w k C pos : Nat) (source copy out : List Bool) :
    Step last 3 (heads pos out) (data w k C source copy out)
      (heads (pos+3) (out++[false])) (data w k C source copy (out++[false])) := by
  have h0:step last ⟨0,heads pos out,data w k C source copy out⟩=
      some ⟨1,heads (pos+1) (out++[false]),data w k C source copy (out++[false])⟩:=by
    simp [step,last]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,heads,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,heads,data,Streaming.write_append]
  have step_more (q : Fin 4) (hq : q=1 ∨ q=2) (p : Nat) (o : List Bool) :
      step last ⟨q,heads p o,data w k C source copy o⟩=
        some ⟨⟨q.val+1,by rcases hq with rfl|rfl <;> decide⟩,
          heads (p+1) o,data w k C source copy o⟩:=by
    rcases hq with rfl|rfl
    all_goals
      simp [step,last]
      apply configuration_ext
      · rfl
      · funext i;fin_cases i <;> simp [applyAction,heads,HeadMove.apply]
      · rfl
  have a:=Timed.single (by rfl : last.halted 0=false) h0
  have b:=Timed.single (by rfl : last.halted 1=false) (step_more 1 (by simp) (pos+1) (out++[false]))
  have c:=Timed.single (by rfl : last.halted 2=false) (step_more 2 (by simp) (pos+1+1) (out++[false]))
  obtain ⟨r,hr,rf,_⟩:=(a.trans (b.trans c)).run (by rfl)
  have result:=Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa only [Nat.add_assoc] using result

theorem monomial_run (w C M : Nat) (ds : List Nat) (pre tail copy out : List Bool)
    (hc : 2*w+1≤C) (hcopy : copy.length≤w)
    (hd : ∀ d∈ds,d<2^w) (hM : ∀ d∈ds,d≤M) :
    ∃ residue : List Bool,residue.length≤w ∧
      Step machine (budget w ds.length M) (heads pre.length out)
        (data w ds.length C (pre++RowTupleFramedBody.word w ds++tail) copy out)
        (heads (pre.length+(RowTupleFramedBody.word w ds).length) (out++ExtIncidence.monomialWord ds))
        (data w ds.length C (pre++RowTupleFramedBody.word w ds++tail) residue (out++ExtIncidence.monomialWord ds)) := by
  have word:RowTupleFramedBody.word w ds=RowTupleFilterLoop.word w ds++RowTupleFrame.trailer:=
    RowTupleFrame.encoded_word w ds hd
  obtain ⟨residue,hres,loop⟩:=loop_run w C M ds pre (RowTupleFrame.trailer++tail) copy (out++[true]) hc hcopy hd hM
  have before:=first_run w ds.length C pre.length (pre++RowTupleFramedBody.word w ds++tail) copy out
  have after:=last_run w ds.length C (pre.length+(RowTupleFilterLoop.word w ds).length)
    (pre++RowTupleFramedBody.word w ds++tail) residue ((out++[true])++ds.flatMap ExtIncidence.block)
  have source:pre++RowTupleFilterLoop.word w ds++(RowTupleFrame.trailer++tail)=pre++RowTupleFramedBody.word w ds++tail:=by
    rw [word];simp only [List.append_assoc]
  rw [source] at loop
  have whole:=(before.seq loop).seq after
  have time:1+1+loopBudget w ds.length M+1+3=budget w ds.length M:=by unfold budget;omega
  rw [time] at whole
  have output:((out++[true])++ds.flatMap ExtIncidence.block)++[false]=out++ExtIncidence.monomialWord ds:=by
    simp [ExtIncidence.monomialWord,List.append_assoc]
  have pos:pre.length+(RowTupleFilterLoop.word w ds).length+3=
      pre.length+(RowTupleFramedBody.word w ds).length:=by rw [word];simp [RowTupleFrame.trailer];omega
  rw [output,pos] at whole
  exact ⟨residue,hres,whole⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleMonomial
