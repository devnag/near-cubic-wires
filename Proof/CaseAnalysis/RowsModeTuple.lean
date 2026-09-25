import Proof.CaseAnalysis.RowsModeTuplePolynomial

/-! The tuple writer runs from empty private tapes. Its actual transitions
allocate the finite cells used by the reusable digit body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleCold
open LocalBitMultitape RecoveryExecution
open CloseoutRowsModeTupleMonomial (heads data)
open CloseoutRowsModeTuplePolynomial
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (w k : Nat) (source out : List Bool) : Fin 7→List Bool:=
  ![source,[],CompareMachine.word w,[],[],out,CompareMachine.word k]
def capacities (w : Nat) : Fin 7→Nat:=![0,1,0,1,2*w+1,0,0]

theorem writer_run (w k M : Nat) (ps : List (List Nat)) (out : List Bool)
    (hk : ∀ ds∈ps,ds.length=k) (hd : ∀ ds∈ps,∀ d∈ds,d<2^w)
    (hM : ∀ ds∈ps,∀ d∈ds,d≤M) :
    ∃ r,runFrom machine (budget w k M ps.length)
      ⟨machine.start,heads 0 out,input w k (sourceWord w ps) out⟩=some r ∧
      r.final.heads=heads (sourceWord w ps).length (out++ps.flatMap ExtIncidence.monomialWord) ∧
      r.final.tapes 0=sourceWord w ps ∧ r.final.tapes 2=CompareMachine.word w ∧
      r.final.tapes 5=out++ps.flatMap ExtIncidence.monomialWord ∧
      r.final.tapes 6=CompareMachine.word k ∧ r.steps≤budget w k M ps.length := by
  obtain ⟨residue,_,time,ht,tr⟩:=remaining w k (2*w+1) M ps [] [] out (by omega) (by simp) hk hd hM
  obtain ⟨base,hbase,bf,_⟩:=tr.run (by
    simp [machine,final,RecoveryCalls.machine,RecoveryCalls.stopped,RecoveryCalls.controlCode])
  have more:=runFrom_moreFuel machine time (budget w k M ps.length-time) _ base hbase
  rw [Nat.add_sub_of_le ht] at more
  have initial:entry 0 w k (2*w+1) ([] : List Bool).length ([]++sourceWord w ps) [] out=
      ZeroPadding.config (capacities w)
        (⟨machine.start,heads 0 out,input w k (sourceWord w ps) out⟩ : Configuration 7 _):=by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> simp [entry,controlConfig,data,input,capacities,ZeroPadding.config,
        ZeroPadding.pad,frame,RepairOrdinary.frame]
  rw [initial] at more
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_unpad machine (capacities w) _ _ base more
  have rh: r.final.heads=heads (sourceWord w ps).length (out++ps.flatMap ExtIncidence.monomialWord):=by
    have h:=congrArg Configuration.heads rf
    rw [bf] at h
    simpa [ZeroPadding.config,final,RecoveryCalls.stopped] using h
  have field (i : Fin 7) (hi : capacities w i=0) :
      r.final.tapes i=data w k (2*w+1) (sourceWord w ps) residue (out++ps.flatMap ExtIncidence.monomialWord) i:=by
    have h:=congrArg (fun c=>c.tapes i) rf
    rw [bf] at h
    simpa only [ZeroPadding.config,hi,ZeroPadding.pad_zero,final,RecoveryCalls.stopped,
      List.nil_append] using h
  exact ⟨r,hr,rh,field 0 rfl,field 2 rfl,field 5 rfl,field 6 rfl,
    rs.le.trans (runFrom_steps_le machine _ _ _ more)⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleCold
