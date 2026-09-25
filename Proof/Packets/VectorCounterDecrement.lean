import Proof.Packets.VectorCounter

/-! Paid descending unary indices for reversed level and mask traversals.
The erased last true bit remains part of the reusable physical allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def decrement : Machine 1 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q scan=>if q.val=0 then
    some (if scan 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>none,fun _=>.left⟩)
    else if q.val=1 then some ⟨2,fun _=>some false,fun _=>.left⟩
    else if q.val=2 then
      some (if scan 0 then ⟨2,fun _=>none,fun _=>.left⟩
        else ⟨3,fun _=>none,fun _=>.right⟩)
    else none

def dcfg (q : Fin 4) (word : List Bool) (pos : Nat) : Configuration 1 4 :=
  ⟨q,fun _=>pos,fun _=>word⟩

theorem decrement_advance (n k : Nat) (hk : k<n) :
    step decrement (dcfg 0 (CompareMachine.word n) (k+1))=
      some (dcfg 0 (CompareMachine.word n) (k+2)) := by
  simp [step,decrement,dcfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem decrement_prefix (n k : Nat) (hk : k≤n) :
    Timed decrement k (dcfg 0 (CompareMachine.word n) 1) (dcfg 0 (CompareMachine.word n) (k+1)) := by
  induction k with
  | zero => exact Timed.refl decrement _
  | succ k ih => exact (ih (by omega)).trans (Timed.single (by rfl) (decrement_advance n k (by omega)))

theorem decrement_turn (n : Nat) :
    step decrement (dcfg 0 (CompareMachine.word (n+1)) (n+2))=
      some (dcfg 1 (CompareMachine.word (n+1)) (n+1)) := by
  simp [step,decrement,dcfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem decrement_erase (n : Nat) :
    step decrement (dcfg 1 (CompareMachine.word (n+1)) (n+1))=
      some (dcfg 2 (UnaryTemplate.tape n) n) := by
  simp [step,decrement,dcfg]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · funext i
    change writeTapeBit (CompareMachine.word (n+1)) (n+1) false=UnaryTemplate.tape n
    rw [←word_succ]
    have h:=PhysicalBankCopy.write_at (CompareMachine.word n) [] true false
    simpa only [CompareMachine.word,UnaryTemplate.tape,List.cons_append,List.length_cons,
      List.length_replicate] using h

theorem decrement_back (n k : Nat) (hk : k<n) :
    step decrement (dcfg 2 (UnaryTemplate.tape n) (k+1))=
      some (dcfg 2 (UnaryTemplate.tape n) k) := by
  simp [step,decrement,dcfg,Configuration.scanned,UnaryTemplate.tape_mark n k hk]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem decrement_stop (n : Nat) :
    step decrement (dcfg 2 (UnaryTemplate.tape n) 0)=some (dcfg 3 (UnaryTemplate.tape n) 1) := by
  simp [step,decrement,dcfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem decrement_return (n k : Nat) (hk : k≤n) :
    Timed decrement (k+1) (dcfg 2 (UnaryTemplate.tape n) k) (dcfg 3 (UnaryTemplate.tape n) 1) := by
  induction k with
  | zero => exact Timed.single (by rfl) (decrement_stop n)
  | succ k ih =>
    have h:=(Timed.single (by rfl) (decrement_back n k (by omega))).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem decrement_run (n : Nat) :
    Step decrement (2*n+4) (fun _=>1) (fun _=>CompareMachine.word (n+1))
      (fun _=>1) (fun _=>UnaryTemplate.tape n) := by
  have h:=(decrement_prefix (n+1) (n+1) le_rfl).trans
    ((Timed.single (by rfl) (decrement_turn n)).trans
      ((Timed.single (by rfl) (decrement_erase n)).trans (decrement_return n n le_rfl)))
  have fuel : (n+1)+(1+(1+(n+1)))=2*n+4 := by omega
  rw [fuel] at h
  obtain ⟨r,rr,rf,_⟩:=h.run (by rfl)
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem padded_template_word (n capacity : Nat) (hcap : n+2≤capacity) :
    ZeroPadding.pad capacity (UnaryTemplate.tape n)=ZeroPadding.pad capacity (CompareMachine.word n) := by
  have e : capacity-(n+1)=(capacity-(n+2))+1 := by omega
  simp only [ZeroPadding.pad,UnaryTemplate.tape,CompareMachine.word,List.length_cons,
    List.length_append,List.length_replicate,List.cons_append,List.append_assoc]
  rw [e,List.replicate_succ]
  rfl

theorem decrement_padded (n capacity : Nat) (hcap : n+2≤capacity) :
    Step decrement (2*n+4) (fun _=>1)
      (fun _=>ZeroPadding.pad capacity (CompareMachine.word (n+1)))
      (fun _=>1) (fun _=>ZeroPadding.pad capacity (CompareMachine.word n)) := by
  have h:=(decrement_run n).pad (fun _=>capacity)
  exact h.congr rfl (by funext i;exact padded_template_word n capacity hcap)

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
