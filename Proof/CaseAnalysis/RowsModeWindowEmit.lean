import Proof.CaseAnalysis.RowsModeWindowBoundary

/-! A fixed three-call controller emits one guarded elementary summand.
Its zero-population branch physically writes the constant monomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowEmit
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body : Σ s,Machine 60 s:=⟨_,elementary⟩
noncomputable def sizes : Fin 3→Nat:=![5,body.1,3]
noncomputable def programs : (i : Fin 3)→Machine 60 (sizes i)
  | ⟨0,_⟩=>CloseoutRowsModeWindowSelect.machine
  | ⟨1,_⟩=>body.2
  | ⟨2,_⟩=>CloseoutRowsModeWindowConstant.machine
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (i : Fin 3) (q : Fin (sizes i)) (_ : Fin 60→Bool) : Option (Fin 3):=
  if i=0 then if q.val=3 then some 1 else if q.val=4 then some 2 else none else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next
noncomputable def entry (i : Fin 3) (H : Fin 60→Nat) (A : Fin 60→List Bool):=
  controlConfig (RecoveryCalls.code sizes i) (⟨(programs i).start,H,A⟩ : Configuration 60 (sizes i))
noncomputable def final (H : Fin 60→Nat) (A : Fin 60→List Bool):=RecoveryCalls.stopped sizes H A
def word (v a M : Nat) (guard : Bool):=if guard then
  if M=0 then if a=0 then [true,false] else [] else CloseoutRowsModeElementary.bodyWord v a M else []

theorem finish (n fuel : Nat) (H H' : Fin 60→Nat) (A A' : Fin 60→List Bool)
    (hn : n≤fuel) (tr : Timed machine n (entry 0 H A) (final H' A')) :
    Step machine fuel H A H' A':=by
  obtain ⟨r,hr,rf,_⟩:=tr.run (by simp [machine,final,RecoveryCalls.machine,RecoveryCalls.stopped])
  exact (Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).enlarge hn

theorem selected_skip (H : Fin 60→Nat) (A : Fin 60→List Bool)
    (r : ExecutionReceipt 60 5)
    (hr : runFrom CloseoutRowsModeWindowSelect.machine 2 ⟨CloseoutRowsModeWindowSelect.machine.start,H,A⟩=some r)
    (rf : r.final=⟨2,H,A⟩) : Step machine 3 H A H A:=by
  obtain ⟨n,hn,tr⟩:=stop_receipt sizes programs 0 next 0 2 _ r hr (by rw [rf];rfl)
  rw [rf] at tr
  exact finish n 3 H H A A hn tr

theorem selected_call (j : Fin 3) (H H' : Fin 60→Nat) (A A' : Fin 60→List Bool)
    (r : ExecutionReceipt 60 5)
    (hr : runFrom CloseoutRowsModeWindowSelect.machine 2 ⟨CloseoutRowsModeWindowSelect.machine.start,H,A⟩=some r)
    (rh : r.final.heads=H) (rt : r.final.tapes=A)
    (hn : next 0 r.final.control r.final.scanned=some j) (hj : j≠0)
    (fuel : Nat) (worker : Step (programs j) fuel H A H' A') :
    Step machine (fuel+4) H A H' A':=by
  obtain ⟨n,hn',first⟩:=call_receipt sizes programs 0 next 0 j 2 _ r hr hn
  have same:RecoveryCalls.restarted (programs j) r.final.heads r.final.tapes=
      (⟨(programs j).start,H,A⟩ : Configuration 60 (sizes j)):=by
    apply configuration_ext
    · rfl
    · exact rh
    · exact rt
  rw [same] at first
  obtain ⟨s,hs,sh,st,_⟩:=worker
  obtain ⟨m,hm,last⟩:=stop_receipt sizes programs 0 next j fuel _ s hs (by simp [next,hj])
  rw [sh,st] at last
  exact finish (n+m) (fuel+4) H H' A A' (by omega) (first.trans last)

theorem emit_run (v u M a offset b scratch degree target C : Nat)
    (nonzero guard : Bool) (out : List Bool) (hMv : M≤2^v)
    (hmeta : 2*v+a+3≤C) (hC : CloseoutRowsModeElementary.budget v a M+1≤C) :
    Step machine (CloseoutRowsModeElementaryReusable.budget v a M C+6) (heads out)
      (data v u M a offset b scratch degree target C nonzero guard out)
      (heads (out++word v a M guard))
      (data v u M a offset b scratch degree target C nonzero guard (out++word v a M guard)):=by
  obtain ⟨r,hr,rf,_⟩:=select_run v u M a offset b scratch degree target C nonzero guard out
  cases guard
  · have hrf:r.final=⟨2,heads out,data v u M a offset b scratch degree target C nonzero false out⟩:=by
      simpa [CloseoutRowsModeWindowSelect.result] using rf
    simpa only [word,Bool.false_eq_true,if_false,List.append_nil] using
      (selected_skip _ _ r hr hrf).enlarge (by omega : 3≤CloseoutRowsModeElementaryReusable.budget v a M C+6)
  · by_cases hM:M=0
    · by_cases ha:a=0
      · have hn:next 0 r.final.control r.final.scanned=some 2:=by
          rw [rf];simp [next,CloseoutRowsModeWindowSelect.result,hM,ha]
        have result:=selected_call 2 _ _ _ _ r hr (congrArg Configuration.heads rf)
          (congrArg Configuration.tapes rf) hn (by decide) 2
          (constant_run v u M a offset b scratch degree target C nonzero true out)
        simpa [word,hM,ha] using result.enlarge
          (by omega : 2+4≤CloseoutRowsModeElementaryReusable.budget v a M C+6)
      · have hrf:r.final=⟨2,heads out,data v u M a offset b scratch degree target C nonzero true out⟩:=by
          simpa [CloseoutRowsModeWindowSelect.result,hM,show 0<a by omega] using rf
        simpa [word,hM,ha] using (selected_skip _ _ r hr hrf).enlarge
          (by omega : 3≤CloseoutRowsModeElementaryReusable.budget v a M C+6)
    · have hn:next 0 r.final.control r.final.scanned=some 1:=by
        rw [rf];simp [next,CloseoutRowsModeWindowSelect.result,show 0<M by omega]
      have result:=selected_call 1 _ _ _ _ r hr (congrArg Configuration.heads rf)
        (congrArg Configuration.tapes rf) hn (by decide) _
        (elementary_run v u M a offset b scratch degree target C nonzero true out (by omega) hMv hmeta hC)
      simpa [word,hM] using result.enlarge
        (by omega : CloseoutRowsModeElementaryReusable.budget v a M C+4≤CloseoutRowsModeElementaryReusable.budget v a M C+6)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeWindowEmit
