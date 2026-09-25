import Proof.Packets.PacketBankPrimitives

/-! Physical unary loop-coordinate updates. Counters have their actual false
sentinel and return to head one, so they can directly drive packet lookup. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def increment : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q scan=>if q.val=0 then
    some (if scan 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>some true,fun _=>.left⟩)
    else if q.val=1 then
      some (if scan 0 then ⟨1,fun _=>none,fun _=>.left⟩
        else ⟨2,fun _=>none,fun _=>.right⟩)
    else none

def cfg (q : Fin 3) (n pos : Nat) : Configuration 1 3 :=
  ⟨q,fun _=>pos,fun _=>CompareMachine.word n⟩

theorem advance (n k : Nat) (hk : k<n) :
    step increment (cfg 0 n (k+1))=some (cfg 0 n (k+2)) := by
  simp [step,increment,cfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem advance_prefix (n k : Nat) (hk : k≤n) :
    Timed increment k (cfg 0 n 1) (cfg 0 n (k+1)) := by
  induction k with
  | zero => exact Timed.refl increment _
  | succ k ih => exact (ih (by omega)).trans (Timed.single (by rfl) (advance n k (by omega)))

theorem word_succ (n : Nat) : CompareMachine.word n++[true]=CompareMachine.word (n+1) := by
  simp only [CompareMachine.word,List.replicate_add,List.replicate_one,List.cons_append]

theorem bump (n : Nat) : step increment (cfg 0 n (n+1))=some (cfg 1 (n+1) n) := by
  simp [step,increment,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · funext i
    change writeTapeBit (CompareMachine.word n) (n+1) true=CompareMachine.word (n+1)
    rw [←word_succ]
    simpa only [CompareMachine.word,List.length_cons,List.length_replicate] using
      Streaming.write_append (CompareMachine.word n) true

theorem back (n k : Nat) (hk : k<n) :
    step increment (cfg 1 n (k+1))=some (cfg 1 n k) := by
  simp [step,increment,cfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem stop (n : Nat) : step increment (cfg 1 n 0)=some (cfg 2 n 1) := by
  simp [step,increment,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;simp [applyAction,HeadMove.apply]
  · rfl

theorem return_run (n k : Nat) (hk : k≤n) :
    Timed increment (k+1) (cfg 1 n k) (cfg 2 n 1) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop n)
  | succ k ih =>
    have h:=(Timed.single (by rfl) (back n k (by omega))).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem increment_run (n : Nat) :
    Step increment (2*n+2) (fun _=>1) (fun _=>CompareMachine.word n)
      (fun _=>1) (fun _=>CompareMachine.word (n+1)) := by
  have h:=(advance_prefix n n le_rfl).trans
    ((Timed.single (by rfl) (bump n)).trans (return_run (n+1) n (by omega)))
  have fuel : n+(1+(n+1))=2*n+2 := by omega
  rw [fuel] at h
  obtain ⟨r,rr,rf,_⟩:=h.run (by rfl)
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

theorem increment_padded (n capacity : Nat) :
    Step increment (2*n+2) (fun _=>1) (fun _=>ZeroPadding.pad capacity (CompareMachine.word n))
      (fun _=>1) (fun _=>ZeroPadding.pad capacity (CompareMachine.word (n+1))) :=
  (increment_run n).pad (fun _=>capacity)

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
