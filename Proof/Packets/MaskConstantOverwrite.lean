import Proof.Packets.MaskConstant
import Proof.Packets.PhysicalBankCopy

/-! The existing constant-mask machine overwrites an arbitrary resident
block. Its runtime still depends only on the actual width template. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskConstant
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch

theorem overwrite_step (B k : Nat) (pre rest post : List Bool) (bit : Bool) (hk : k<B) :
    step maskMachine (cfg 0 B (k+1) pre.length (pre++bit::rest++post))=
      some (cfg 0 B (k+2) (pre.length+1) (pre++false::rest++post)) := by
  have ht:=PhysicalBankCopy.write_at pre (rest++post) bit false
  simp [step,maskMachine,cfg,Configuration.scanned,UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;>simp [applyAction,ht]

theorem overwrite_copy (B n done : Nat) (pre old post : List Bool)
    (hlen : old.length=n) (hn : done+n=B) :
    Timed maskMachine n (cfg 0 B (done+1) pre.length (pre++old++post))
      (cfg 0 B (B+1) (pre.length+n) (pre++List.replicate n false++post)) := by
  induction n generalizing done pre old with
  | zero=>
    have ho:old=[]:=List.length_eq_zero_iff.mp hlen
    subst old
    have hd:done=B:=by omega
    subst done
    simpa using Timed.refl maskMachine (cfg 0 B (B+1) pre.length (pre++post))
  | succ n ih=>
    cases old with
    | nil=>simp at hlen
    | cons bit rest=>
      have hr:rest.length=n:=by simpa using hlen
      have first:=Timed.single (by rfl) (overwrite_step B done pre rest post bit (by omega))
      have last:=ih (done+1) (pre++[false]) rest hr (by omega)
      have h:=first.trans (by simpa only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] using last)
      simpa [List.append_assoc,List.replicate_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem overwrite_run (B : Nat) (pre old post : List Bool) (hlen : old.length=B) :
    Step maskMachine (2*B+2) ![1,pre.length] ![UnaryTemplate.tape B,pre++old++post]
      ![1,pre.length] ![UnaryTemplate.tape B,pre++List.replicate B false++post] := by
  have first:=overwrite_copy B B 0 pre old post hlen (by omega)
  have second:=Timed.single (by rfl) (turn B (pre.length+B) (pre++List.replicate B false++post))
  have last:=back B B pre.length (pre++List.replicate B false++post) le_rfl
  have h:=first.trans (second.trans last)
  have fuel : B+(1+(B+1))=2*B+2:=by omega
  rw [fuel] at h
  obtain ⟨r,hr,hf,hs⟩:=h.run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskConstant
