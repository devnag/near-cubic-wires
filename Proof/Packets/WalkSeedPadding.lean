import Proof.Packets.WalkRawSegment

/-! Determine the low padding bit from the actual rank tape and skip it.
The rank tape and source word are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedPadding
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine : Machine 2 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q bits=>if q.val<2 then some (if bits 0 then
      ⟨if q.val=0 then 1 else 0,fun _=>none,![.right,.stay]⟩ else
      ⟨2,fun _=>none,![.left,if q.val=0 then .right else .stay]⟩)
    else if q.val=2 then some (if bits 0 then
      ⟨2,fun _=>none,![.left,.stay]⟩ else
      ⟨3,fun _=>none,![.right,.stay]⟩) else none

def parityState (i : Nat) : Fin 4 := ⟨i%2,by omega⟩
def padding (B : Nat) : Nat:=if B%2=0 then 1 else 0
def cfg (q : Fin 4) (B driver pos : Nat) (source : List Bool) : Configuration 2 4 :=
  ⟨q,![driver,pos],![UnaryTemplate.tape B,source]⟩

theorem bit_step (B i pos : Nat) (hi : i<B) (source : List Bool) :
    step machine (cfg (parityState i) B (i+1) pos source)=
      some (cfg (parityState (i+1)) B (i+2) pos source) := by
  have hm:i%2<2:=Nat.mod_lt _ (by decide)
  have hw:=UnaryTemplate.tape_mark B i hi
  by_cases h:i%2=0
  · have hn:(i+1)%2=1:=by omega
    simp [step,machine,cfg,parityState,Configuration.scanned,hw,h,hn]
    apply configuration_ext
    · rfl
    · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
    · rfl
  · have ho:i%2=1:=by omega
    have hn:(i+1)%2=0:=by omega
    simp [step,machine,cfg,parityState,Configuration.scanned,hw,ho,hn]
    apply configuration_ext
    · rfl
    · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
    · rfl

theorem stop_step (B pos : Nat) (source : List Bool) :
    step machine (cfg (parityState B) B (B+1) pos source)=
      some (cfg 2 B B (pos+padding B) source) := by
  have hm:B%2<2:=Nat.mod_lt _ (by decide)
  by_cases h:B%2=0
  · simp [step,machine,cfg,parityState,Configuration.scanned,h,padding]
    apply configuration_ext
    · rfl
    · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
    · rfl
  · have ho:B%2=1:=by omega
    simp [step,machine,cfg,parityState,Configuration.scanned,ho,padding]
    apply configuration_ext
    · rfl
    · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
    · rfl

theorem forward_prefix (B n i pos : Nat) (hi : i+n=B) (source : List Bool) :
    Timed machine (n+1) (cfg (parityState i) B (i+1) pos source)
      (cfg 2 B B (pos+padding B) source) := by
  induction n generalizing i with
  | zero=>
    have h:i=B:=by omega
    subst i
    exact Timed.single (by simp [machine,cfg,parityState];omega) (stop_step B pos source)
  | succ n ih=>
    have h:=(Timed.single (by simp [machine,cfg,parityState];omega)
      (bit_step B i pos (by omega) source)).trans (ih (i+1) (by omega))
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem back_step (B n pos : Nat) (hn : n<B) (source : List Bool) :
    step machine (cfg 2 B (n+1) pos source)=some (cfg 2 B n pos source) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark B n hn]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
  · rfl

theorem end_step (B pos : Nat) (source : List Bool) :
    step machine (cfg 2 B 0 pos source)=some (cfg 3 B 1 pos source) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
  · rfl

theorem back_prefix (B n pos : Nat) (hn : n≤B) (source : List Bool) :
    Timed machine (n+1) (cfg 2 B n pos source) (cfg 3 B 1 pos source) := by
  induction n with
  | zero=>exact Timed.single (by rfl) (end_step B pos source)
  | succ n ih=>
    have h:=(Timed.single (by rfl) (back_step B n pos (by omega) source)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem run (B pos : Nat) (source : List Bool) :
    Step machine (2*B+2) (![1,pos]) (![UnaryTemplate.tape B,source])
      (![1,pos+padding B]) (![UnaryTemplate.tape B,source]) := by
  have h:=(forward_prefix B B 0 pos (by omega) source).trans
    (back_prefix B B (pos+padding B) le_rfl source)
  have ht:B+1+(B+1)=2*B+2:=by omega
  rw [ht] at h
  obtain ⟨r,rr,rf,_⟩:=h.run (by rfl)
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end Theorem25Completion.WalkSeedPadding
