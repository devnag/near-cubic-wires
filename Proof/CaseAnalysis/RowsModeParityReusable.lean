import Proof.Amplification.RecoveryFocusDock
import Proof.CaseAnalysis.RowsModeParity

/-! The actual binomial parity scan pays its recorded return, retaining
both scalar frames and the accumulated guard for the next coefficient. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeParityReusable
open LocalBitMultitape RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Rewind.machine CloseoutRowsModeParity.machine
def input (w n k C : Nat) (old : Bool) : Fin 4→List Bool:=
  ![frame (binary w n),frame (binary w k),[old],List.replicate C false]

theorem parity_ready (w n k C : Nat) (old : Bool) (hn : n<2^w) (hk : k<2^w)
    (hC : 2*w+1≤C) : ReadyRun machine (4*w+4) (input w n k C old)
      (input w n k C (old&&(n.choose k%2==1))):=by
  have tr:=CloseoutRowsModeParity.scan_prefix (binary w n) (binary w k) [] [] [] [] old (by simp)
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,binary_length,
    CloseoutRowsModeParity.guard_binary w n k hn hk] at tr
  obtain ⟨a,ha,af,as⟩:=tr.run (by rfl)
  have atapes:=congrArg Configuration.tapes af
  have initial:CloseoutRowsModeParity.cfg 0 (frame (binary w n)) (frame (binary w k)) 0 0 old=
      initialConfiguration CloseoutRowsModeParity.machine ![frame (binary w n),frame (binary w k),[old]]:=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  rw [initial] at ha
  obtain ⟨r,hr,rt,rz,rh,rs,_⟩:=Rewind.Workspace.reset_workspace CloseoutRowsModeParity.machine _ _ a ha C
  rw [as] at hr rz rs
  have time:2*(2*w+1)+2=4*w+4:=by omega
  rw [time] at hr rs
  have hin:Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool)
      ![frame (binary w n),frame (binary w k),[old]] (fun _=>List.replicate C false)=input w n k C old:=by
    funext i;fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨r,hr,?_,rh,rs⟩
  funext i;fin_cases i
  · exact (rt 0).trans (congrFun atapes 0)
  · exact (rt 1).trans (congrFun atapes 1)
  · exact (rt 2).trans (congrFun atapes 2)
  · change r.final.tapes 3=List.replicate C false
    simpa [max_eq_left hC,Fin.natAdd] using rz

end NearCubicWires.RepairOrdinary.CloseoutRowsModeParityReusable
