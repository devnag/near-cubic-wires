import Proof.Packets.WalkUnframe

/-! Copy a raw bit segment with an actual unary driver. A noninitial driver
position permits the upper Toeplitz diagonal to have one fewer bit. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkRawSegment
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then some (if bits 0 then
      ⟨0,![none,none,some (bits 1)],fun _=>.right⟩ else
      ⟨1,fun _=>none,![.left,.stay,.stay]⟩)
    else if q.val=1 then some (if bits 0 then
      ⟨1,fun _=>none,![.left,.stay,.stay]⟩ else
      ⟨2,fun _=>none,![.right,.stay,.stay]⟩) else none

def cfg (q : Fin 3) (B driver pos : Nat) (source out : List Bool) : Configuration 3 3 :=
  ⟨q,![driver,pos,out.length],![UnaryTemplate.tape B,source,out]⟩

theorem bit_step (B i : Nat) (hi : i<B) (pre tail out : List Bool) (b : Bool) :
    step machine (cfg 0 B (i+1) pre.length (pre++b::tail) out)=
      some (cfg 0 B (i+2) (pre.length+1) (pre++b::tail) (out++[b])) := by
  have hw:=UnaryTemplate.tape_mark B i hi
  have hb:=Streaming.read_append pre tail b
  simp [step,machine,cfg,Configuration.scanned,hw,hb]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
  · funext j;fin_cases j <;>simp [applyAction,Streaming.write_append]

theorem stop_step (B pos : Nat) (source out : List Bool) :
    step machine (cfg 0 B (B+1) pos source out)=some (cfg 1 B B pos source out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
  · rfl

theorem copy_prefix (B : Nat) (bits : List Bool) (hb : bits.length≤B)
    (pre tail out : List Bool) :
    Timed machine (bits.length+1)
      (cfg 0 B (B-bits.length+1) pre.length (pre++bits++tail) out)
      (cfg 1 B B (pre.length+bits.length) (pre++bits++tail) (out++bits)) := by
  induction bits generalizing pre out with
  | nil=>simpa using Timed.single (by rfl) (stop_step B pre.length (pre++tail) out)
  | cons b bits ih=>
    have hi:B-(b::bits).length<B := by simp only [List.length_cons] at hb ⊢;omega
    have hs:=bit_step B (B-(b::bits).length) hi pre (bits++tail) out b
    have hd:B-(b::bits).length+2=B-bits.length+1 := by simp only [List.length_cons] at hb ⊢;omega
    rw [hd] at hs
    have htail:=ih (by simp only [List.length_cons] at hb;omega) (pre++[b]) (out++[b])
    have h:= (Timed.single (by rfl) hs).trans (by simpa [List.append_assoc] using htail)
    simpa [List.length_cons,List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem back_step (B n pos : Nat) (hn : n<B) (source out : List Bool) :
    step machine (cfg 1 B (n+1) pos source out)=some (cfg 1 B n pos source out) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark B n hn]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
  · rfl

theorem end_step (B pos : Nat) (source out : List Bool) :
    step machine (cfg 1 B 0 pos source out)=some (cfg 2 B 1 pos source out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;>simp [applyAction,HeadMove.apply]
  · rfl

theorem back_prefix (B n pos : Nat) (hn : n≤B) (source out : List Bool) :
    Timed machine (n+1) (cfg 1 B n pos source out) (cfg 2 B 1 pos source out) := by
  induction n with
  | zero=>exact Timed.single (by rfl) (end_step B pos source out)
  | succ n ih=>
    have h:=(Timed.single (by rfl) (back_step B n pos (by omega) source out)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem run (B : Nat) (bits : List Bool) (hb : bits.length≤B) (pre tail out : List Bool) :
    Step machine (bits.length+B+2)
      (![B-bits.length+1,pre.length,out.length]) (![UnaryTemplate.tape B,pre++bits++tail,out])
      (![1,pre.length+bits.length,(out++bits).length]) (![UnaryTemplate.tape B,pre++bits++tail,out++bits]) := by
  have h:=(copy_prefix B bits hb pre tail out).trans
    (back_prefix B B (pre.length+bits.length) le_rfl (pre++bits++tail) (out++bits))
  have ht:bits.length+1+(B+1)=bits.length+B+2 := by omega
  rw [ht] at h
  obtain ⟨r,rr,rf,_⟩:=h.run (by rfl)
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end Theorem25Completion.WalkRawSegment
