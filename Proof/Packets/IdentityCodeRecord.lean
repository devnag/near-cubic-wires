import Proof.Packets.NativeLiteralCode

/-! Direct native singleton emission from the actual unary occurrence index.
No pairing or supplied framed binary code is used. Both the retained counter
and its cursor are restored while every output framing cell is written. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeRecord
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 2 9 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==8
  rule:=fun q scan=>
    if q.val=0 then some ⟨1,![none,some true],![.stay,.right]⟩
    else if q.val=1 then some ⟨2,![none,some true],![.stay,.right]⟩
    else if q.val=2 then some (if scan 0 then ⟨2,![none,some true],![.right,.right]⟩
      else ⟨3,fun _=>none,![.left,.stay]⟩)
    else if q.val=3 then some (if scan 0 then ⟨3,fun _=>none,![.left,.stay]⟩
      else ⟨4,fun _=>none,![.right,.stay]⟩)
    else if q.val=4 then some ⟨5,![none,some false],![.stay,.right]⟩
    else if q.val=5 then some ⟨6,![none,some false],![.stay,.right]⟩
    else if q.val=6 then some ⟨7,![none,some false],![.stay,.right]⟩
    else if q.val=7 then some ⟨8,![none,some false],![.stay,.right]⟩
    else none

def cfg (q : Fin 9) (n h : Nat) (out : List Bool) : Configuration 2 9 :=
  ⟨q,![h,out.length],![CompareMachine.word n,out]⟩

theorem mark (q q' : Fin 9) (bit : Bool)
    (hq : (q,q',bit)∈[(0,1,true),(1,2,true),(4,5,false),(5,6,false),(6,7,false),(7,8,false)])
    (n h : Nat) (out : List Bool) :
    step machine (cfg q n h out)=some (cfg q' n h (out++[bit])) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hq
  rcases hq with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|
    ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  all_goals
    simp [step,machine,cfg]
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy_step (n k : Nat) (out : List Bool) (hk : k<n) :
    step machine (cfg 2 n (k+1) out)=some (cfg 2 n (k+2) (out++[true])) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.read_mark,hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy (n k done : Nat) (out : List Bool) (hk : done+k=n) :
    Timed machine k (cfg 2 n (done+1) out)
      (cfg 2 n (n+1) (out++List.replicate k true)) := by
  induction k generalizing done out with
  | zero=>have hd : done=n := by omega
          subst done
          simpa using Timed.refl machine (cfg 2 n (n+1) out)
  | succ k ih=>
    have first:=Timed.single (by rfl) (copy_step n done out (by omega))
    have rest:=ih (done+1) (out++[true]) (by omega)
    have h:=first.trans (by simpa only [Nat.add_assoc] using rest)
    simpa [List.replicate_succ,List.append_assoc,Nat.add_comm] using h

theorem turn (n : Nat) (out : List Bool) :
    step machine (cfg 2 n (n+1) out)=some (cfg 3 n n out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_step (n k : Nat) (out : List Bool) (hk : k<n) :
    step machine (cfg 3 n (k+1) out)=some (cfg 3 n k out) := by
  simp [step,machine,cfg,Configuration.scanned,CompareMachine.read_mark,hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_stop (n : Nat) (out : List Bool) :
    step machine (cfg 3 n 0 out)=some (cfg 4 n 1 out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back (n k : Nat) (out : List Bool) (hk : k≤n) :
    Timed machine (k+1) (cfg 3 n k out) (cfg 4 n 1 out) := by
  induction k with
  | zero=>simpa using Timed.single (by rfl) (back_stop n out)
  | succ k ih=>
    have h:=(Timed.single (by rfl) (back_step n k out (by omega))).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem run (n : Nat) (out : List Bool) :
    Step machine (2*n+8) ![1,out.length] ![CompareMachine.word n,out]
      ![1,(out++NativeLiteralCode.word n).length] ![CompareMachine.word n,out++NativeLiteralCode.word n] := by
  have a:=Timed.single (by rfl) (mark 0 1 true (by simp) n 1 out)
  have b:=Timed.single (by rfl) (mark 1 2 true (by simp) n 1 (out++[true]))
  have c:=copy n n 0 ((out++[true])++[true]) (by omega)
  let mid:=((out++[true])++[true])++List.replicate n true
  have d:=Timed.single (by rfl) (turn n mid)
  have e:=back n n mid le_rfl
  have f:=Timed.single (by rfl) (mark 4 5 false (by simp) n 1 mid)
  have g:=Timed.single (by rfl) (mark 5 6 false (by simp) n 1 (mid++[false]))
  have h:=Timed.single (by rfl) (mark 6 7 false (by simp) n 1 ((mid++[false])++[false]))
  have j:=Timed.single (by rfl) (mark 7 8 false (by simp) n 1 (((mid++[false])++[false])++[false]))
  have all:=a.trans (b.trans (c.trans (d.trans (e.trans (f.trans (g.trans (h.trans j)))))))
  obtain ⟨r,rr,rf,_⟩:=all.run (by rfl)
  have actual:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa [cfg,mid,NativeLiteralCode.word,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,two_mul] using actual

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeRecord
