import Proof.Rows.MaskProductRowReady

/-! Actual raw-mask framing with a physically incremented record counter.
The dummy tape is read-only; its cursor pays for restoring the width cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
abbrev cfg := @MaskProduct.cfg

def raw : Machine 5 5 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==4
  rule := fun q scan=>if q.val=0 then
    some ⟨if scan 0 then 1 else 2,![none,none,none,some (scan 0),none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,none,none,some (scan 2),none],
      ![.right,.right,.right,.right,.stay]⟩
    else if q.val=2 then some ⟨3,![none,none,none,some false,none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=3 then some ⟨4,![none,none,none,some false,some true],
      ![.stay,.stay,.stay,.right,.right]⟩
    else none

theorem marker_step (B k mh pos : Nat) (dummy source out count : List Bool) (hk : k<B) :
    step raw (cfg 0 B (k+1) mh dummy source pos out count)=
      some (cfg 1 B (k+1) mh dummy source pos (out++[true]) count) := by
  simp [step,raw,cfg,MaskProduct.cfg,Configuration.scanned,UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem value_step (b : Bool) (dummy pre tail out count : List Bool) (B k : Nat) :
    step raw (cfg 1 B (k+1) k dummy (pre++b::tail) pre.length out count)=
      some (cfg 0 B (k+2) (k+1) dummy (pre++b::tail)
        (pre.length+1) (out++[b]) count) := by
  simp [step,raw,cfg,MaskProduct.cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem delimiter_step (B mh pos : Nat) (dummy source out count : List Bool) :
    step raw (cfg 0 B (B+1) mh dummy source pos out count)=
      some (cfg 2 B (B+1) mh dummy source pos (out++[false]) count) := by
  simp [step,raw,cfg,MaskProduct.cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem tag_step (B dh mh pos : Nat) (dummy source out count : List Bool) :
    step raw (cfg 2 B dh mh dummy source pos out count)=
      some (cfg 3 B dh mh dummy source pos (out++[false]) count) := by
  simp [step,raw,cfg,MaskProduct.cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem count_step (B dh mh pos : Nat) (dummy source out count : List Bool) :
    step raw (cfg 3 B dh mh dummy source pos out count)=
      some (cfg 4 B dh mh dummy source pos (out++[false]) (count++[true])) := by
  simp [step,raw,cfg,MaskProduct.cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy_loop (bits dummy pre tail out count : List Bool) (B done : Nat)
    (fit : done+bits.length=B) :
    Timed raw (2*bits.length)
      (cfg 0 B (done+1) done dummy (pre++bits++tail) pre.length out count)
      (cfg 0 B (B+1) B dummy (pre++bits++tail) (pre.length+bits.length)
        (out++Streaming.marks bits) count) := by
  induction bits generalizing pre out done with
  | nil =>
    have h : done=B := by simpa using fit
    subst done
    simpa [Streaming.marks] using Timed.refl raw
      (cfg 0 B (B+1) B dummy (pre++tail) pre.length out count)
  | cons b bits ih =>
    have mark:=Timed.single (by rfl : raw.halted 0=false)
      (marker_step B done done pre.length dummy (pre++b::bits++tail) out count
        (by simp only [List.length_cons] at fit;omega))
    have bit:=Timed.single (by rfl : raw.halted 1=false)
      (value_step b dummy pre (bits++tail) (out++[true]) count B done)
    have rest:=ih (pre++[b]) ((out++[true])++[b]) (done+1)
      (by simp only [List.length_cons] at fit;omega)
    simp only [List.append_assoc,List.cons_append] at mark
    have h:=mark.trans (bit.trans (by
      simpa [List.append_assoc,Nat.add_assoc] using rest))
    have fuel : 1+(1+2*bits.length)=2*(bits.length+1) := by omega
    rw [fuel] at h
    simpa [Streaming.marks,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem raw_run (bits dummy pre tail out count : List Bool) :
    ∃ r,runFrom raw (2*bits.length+3)
      (cfg 0 bits.length 1 0 dummy (pre++bits++tail) pre.length out count)=some r ∧
      r.final=cfg 4 bits.length (bits.length+1) bits.length dummy (pre++bits++tail)
        (pre.length+bits.length) (out++frame bits++[false,false]) (count++[true]) ∧
      r.steps=2*bits.length+3 := by
  have loop:=copy_loop bits dummy pre tail out count bits.length 0 (by omega)
  have finish:=(Timed.single (by rfl : raw.halted 0=false)
    (delimiter_step bits.length bits.length (pre.length+bits.length) dummy (pre++bits++tail)
      (out++Streaming.marks bits) count)).trans
    ((Timed.single (by rfl : raw.halted 2=false)
      (tag_step bits.length (bits.length+1) bits.length (pre.length+bits.length) dummy
        (pre++bits++tail) ((out++Streaming.marks bits)++[false]) count)).trans
      (Timed.single (by rfl : raw.halted 3=false)
        (count_step bits.length (bits.length+1) bits.length (pre.length+bits.length) dummy
          (pre++bits++tail) (((out++Streaming.marks bits)++[false])++[false]) count)))
  have h:=loop.trans finish
  have hf : Streaming.marks bits++[false]=frame bits := by
    simpa only [List.append_nil,RepairOrdinary.frame] using (Streaming.frame_append bits []).symm
  have out_eq : (((out++Streaming.marks bits)++[false])++[false])++[false]=
      out++frame bits++[false,false] := by
    simp only [List.append_assoc] at hf ⊢
    rw [←hf]
    simp only [List.append_assoc,List.singleton_append]
  rw [out_eq] at h
  simpa only [Nat.zero_add] using h.run (by rfl)

abbrev machine := Composition.machine raw MaskProduct.last

theorem row_run (bits dummy pre tail out count : List Bool) :
    ∃ r,runFrom machine (3*bits.length+6)
      (cfg machine.start bits.length 1 0 dummy (pre++bits++tail) pre.length out count)=some r ∧
      r.final=cfg 7 bits.length 1 0 dummy (pre++bits++tail)
        (pre.length+bits.length) (out++frame bits++[false,false]) (count++[true]) ∧
      r.steps=3*bits.length+6 := by
  obtain ⟨first,hr,hf,hs⟩:=raw_run bits dummy pre tail out count
  obtain ⟨second,sr,sf,ss⟩:=MaskProduct.return5_run bits.length 0 (pre.length+bits.length)
    dummy (pre++bits++tail) (out++frame bits++[false,false]) (count++[true])
  have join : Composition.restart first.final MaskProduct.last.start=
      MaskProduct.cfg 0 bits.length (bits.length+1) (0+bits.length) dummy (pre++bits++tail)
        (pre.length+bits.length) (out++frame bits++[false,false]) (count++[true]) := by
    rw [hf]
    simp only [Nat.zero_add]
    rfl
  rw [←join] at sr
  have h:=Composition.run_join raw MaskProduct.last _ _ _ first second hr sr
  have fuel : (2*bits.length+3)+1+(bits.length+2)=3*bits.length+6 := by omega
  rw [fuel] at h
  refine ⟨Composition.joinedReceipt first second,h,?_,?_⟩
  · change Composition.rightConfig 5 second.final=_
    rw [sf]
    rfl
  · change first.steps+1+second.steps=_
    omega

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
