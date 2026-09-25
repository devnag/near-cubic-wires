import Proof.Rows.MaskProductReturn
import Proof.Rows.PhysicalSupportUnion

/-! One actual Cartesian-product row emits a framed union mask and the two
false record tags, and increments a physical unary result counter. The mask
source may be at any position in its retained bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

abbrev values := PhysicalSupportUnion.values

def cfg {s : Nat} (q : Fin s) (B dh mh : Nat) (left right : List Bool)
    (pos : Nat) (out count : List Bool) : Configuration 5 s :=
  ⟨q,![dh,mh,pos,out.length,count.length],![UnaryTemplate.tape B,left,right,out,count]⟩

def raw : Machine 5 5 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==4
  rule := fun q scan=>if q.val=0 then
    some ⟨if scan 0 then 1 else 2,![none,none,none,some (scan 0),none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,none,none,some (scan 1 || scan 2),none],
      ![.right,.right,.right,.right,.stay]⟩
    else if q.val=2 then some ⟨3,![none,none,none,some false,none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=3 then some ⟨4,![none,none,none,some false,some true],
      ![.stay,.stay,.stay,.right,.right]⟩
    else none

theorem marker_step (B k mh pos : Nat) (left right out count : List Bool) (hk : k<B) :
    step raw (cfg 0 B (k+1) mh left right pos out count)=
      some (cfg 1 B (k+1) mh left right pos (out++[true]) count) := by
  simp [step,raw,cfg,Configuration.scanned,UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem value_step (a b : Bool) (mpre mtail pre tail out count : List Bool) (B k : Nat) :
    step raw (cfg 1 B (k+1) mpre.length (mpre++a::mtail) (pre++b::tail) pre.length out count)=
      some (cfg 0 B (k+2) (mpre.length+1) (mpre++a::mtail) (pre++b::tail)
        (pre.length+1) (out++[a || b]) count) := by
  simp [step,raw,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem delimiter_step (B mh pos : Nat) (left right out count : List Bool) :
    step raw (cfg 0 B (B+1) mh left right pos out count)=
      some (cfg 2 B (B+1) mh left right pos (out++[false]) count) := by
  simp [step,raw,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem tag_step (B dh mh pos : Nat) (left right out count : List Bool) :
    step raw (cfg 2 B dh mh left right pos out count)=
      some (cfg 3 B dh mh left right pos (out++[false]) count) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem count_step (B dh mh pos : Nat) (left right out count : List Bool) :
    step raw (cfg 3 B dh mh left right pos out count)=
      some (cfg 4 B dh mh left right pos (out++[false]) (count++[true])) := by
  simp [step,raw,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i;fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem copy_loop (pairs : List (Bool×Bool))
    (mpre mtail pre tail out count : List Bool) (B done : Nat) (fit : done+pairs.length=B) :
    Timed raw (2*pairs.length)
      (cfg 0 B (done+1) mpre.length (mpre++pairs.map Prod.fst++mtail)
        (pre++pairs.map Prod.snd++tail) pre.length out count)
      (cfg 0 B (B+1) (mpre.length+pairs.length) (mpre++pairs.map Prod.fst++mtail)
        (pre++pairs.map Prod.snd++tail) (pre.length+pairs.length)
        (out++Streaming.marks (values pairs)) count) := by
  induction pairs generalizing mpre pre out done with
  | nil =>
    have h : done=B := by simpa using fit
    subst done
    simpa [values,PhysicalSupportUnion.values,Streaming.marks] using Timed.refl raw
      (cfg 0 B (B+1) mpre.length (mpre++mtail) (pre++tail) pre.length out count)
  | cons pair pairs ih =>
    have mark := Timed.single (by rfl : raw.halted 0=false)
      (marker_step B done mpre.length pre.length
        (mpre++pair.1::pairs.map Prod.fst++mtail)
        (pre++pair.2::pairs.map Prod.snd++tail) out count
        (by simp only [List.length_cons] at fit;omega))
    have bit := Timed.single (by rfl : raw.halted 1=false)
      (value_step pair.1 pair.2 mpre (pairs.map Prod.fst++mtail)
        pre (pairs.map Prod.snd++tail) (out++[true]) count B done)
    have rest := ih (mpre++[pair.1]) (pre++[pair.2]) ((out++[true])++[pair.1 || pair.2])
      (done+1) (by simp only [List.length_cons] at fit;omega)
    simp only [List.append_assoc,List.cons_append] at mark
    have h := mark.trans (bit.trans (by
      simpa [List.append_assoc,Nat.add_assoc] using rest))
    have fuel : 1+(1+2*pairs.length)=2*(pairs.length+1) := by omega
    rw [fuel] at h
    simpa [values,PhysicalSupportUnion.values,Streaming.marks,List.append_assoc,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem raw_pairs_run (pairs : List (Bool×Bool)) (mpre mtail pre tail out count : List Bool) :
    ∃ r,runFrom raw (2*pairs.length+3)
      (cfg 0 pairs.length 1 mpre.length (mpre++pairs.map Prod.fst++mtail)
        (pre++pairs.map Prod.snd++tail) pre.length out count)=some r ∧
      r.final=cfg 4 pairs.length (pairs.length+1) (mpre.length+pairs.length)
        (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
        (pre.length+pairs.length) (out++frame (values pairs)++[false,false]) (count++[true]) ∧
      r.steps=2*pairs.length+3 := by
  have loop := copy_loop pairs mpre mtail pre tail out count pairs.length 0 (by omega)
  have finish := (Timed.single (by rfl : raw.halted 0=false)
    (delimiter_step pairs.length (mpre.length+pairs.length) (pre.length+pairs.length)
      (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
      (out++Streaming.marks (values pairs)) count)).trans
    ((Timed.single (by rfl : raw.halted 2=false)
      (tag_step pairs.length (pairs.length+1) (mpre.length+pairs.length) (pre.length+pairs.length)
        (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
        ((out++Streaming.marks (values pairs))++[false]) count)).trans
      (Timed.single (by rfl : raw.halted 3=false)
        (count_step pairs.length (pairs.length+1) (mpre.length+pairs.length) (pre.length+pairs.length)
          (mpre++pairs.map Prod.fst++mtail) (pre++pairs.map Prod.snd++tail)
          (((out++Streaming.marks (values pairs))++[false])++[false]) count)))
  have h:=loop.trans finish
  have hf : Streaming.marks (values pairs)++[false]=frame (values pairs) := by
    simpa only [List.append_nil,RepairOrdinary.frame] using
      (Streaming.frame_append (values pairs) []).symm
  have out_eq : (((out++Streaming.marks (values pairs))++[false])++[false])++[false]=
      out++frame (values pairs)++[false,false] := by
    simp only [List.append_assoc] at hf ⊢
    rw [←hf]
    simp only [List.append_assoc,List.singleton_append]
  rw [out_eq] at h
  simpa only [Nat.zero_add] using h.run (by rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
