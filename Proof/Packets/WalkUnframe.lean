import Proof.MachineModel.Runs

/-! Decode the payload of one actual framed coordinate into raw seed bits. -/
namespace Theorem25Completion.WalkUnframe
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits => if q.val=0 then some
      ⟨if bits 0 then 1 else 2,![none,none],![.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0)],fun _ => .right⟩ else none

def cfg (q : Fin 3) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨q,![pos,out.length],![source,out]⟩

theorem marker_step (b : Bool) (pre suffix out : List Bool) :
    step machine (cfg 0 (pre++b::suffix) pre.length out)=
      some (cfg (if b then 1 else 2) (pre++b::suffix) (pre.length+1) out) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;>rfl

theorem bit_step (b : Bool) (pre suffix out : List Bool) :
    step machine (cfg 1 (pre++b::suffix) pre.length out)=
      some (cfg 0 (pre++b::suffix) (pre.length+1) (out++[b])) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i
    fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy_prefix (pre bits suffix out : List Bool) :
    Timed machine (2*bits.length+1)
      (cfg 0 (pre++frame bits++suffix) pre.length out)
      (cfg 2 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (out++bits)) := by
  induction bits generalizing pre out with
  | nil =>
    simpa only [frame,RepairOrdinary.frame,List.length_nil,Nat.mul_zero,Nat.add_zero,
      List.append_assoc,List.cons_append,List.nil_append,List.append_nil,Bool.false_eq_true,↓reduceIte] using
      Timed.single (by rfl : machine.halted (0 : Fin 3)=false) (marker_step false pre suffix out)
  | cons b bs ih =>
    let source := pre++frame (b::bs)++suffix
    have hm : step machine (cfg 0 source pre.length out)=
        some (cfg 1 source (pre.length+1) out) := by
      simpa only [source,frame,RepairOrdinary.frame,List.append_assoc,List.cons_append,↓reduceIte] using
        marker_step true pre (b::frame bs++suffix) out
    have hb : step machine (cfg 1 source (pre.length+1) out)=
        some (cfg 0 source (pre.length+2) (out++[b])) := by
      have h := bit_step b (pre++[true]) (frame bs++suffix) out
      simpa only [source,frame,RepairOrdinary.frame,List.length_append,List.length_singleton,List.append_assoc,
        List.cons_append,List.nil_append,Nat.add_assoc] using h
    have he : (pre++[true,b])++frame bs++suffix=source := by
      simp only [source,frame,RepairOrdinary.frame,List.append_assoc,List.cons_append,List.nil_append]
    have htail := ih (pre++[true,b]) (out++[b])
    rw [he] at htail
    have hp : (pre++[true,b]).length=pre.length+2 := by simp
    rw [hp] at htail
    have h0 := (Timed.single (by rfl : machine.halted (0 : Fin 3)=false) hm).trans
      ((Timed.single (by rfl : machine.halted (1 : Fin 3)=false) hb).trans htail)
    have htime : 1+(1+(2*bs.length+1))=2*(b::bs).length+1 := by simp; omega
    have hpos : pre.length+2+2*bs.length+1=pre.length+2*(b::bs).length+1 := by simp; omega
    rw [htime,hpos] at h0
    simpa only [source,frame,RepairOrdinary.frame,List.append_assoc,List.cons_append,List.nil_append] using h0

theorem copy_run (pre bits suffix out : List Bool) :
    ∃ r,runFrom machine (2*bits.length+1)
      (cfg 0 (pre++frame bits++suffix) pre.length out)=some r ∧
      r.final=cfg 2 (pre++frame bits++suffix) (pre.length+2*bits.length+1) (out++bits) ∧
      r.steps=2*bits.length+1 :=
  (copy_prefix pre bits suffix out).run (by rfl)

theorem run (pre bits tail out : List Bool) :
    Step machine (2*bits.length+1) (![pre.length,out.length]) (![pre++frame bits++tail,out])
      (![pre.length+2*bits.length+1,(out++bits).length]) (![pre++frame bits++tail,out++bits]) := by
  obtain ⟨r,rr,rf,_⟩:=copy_run pre bits tail out
  exact Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end Theorem25Completion.WalkUnframe
