import Proof.Packets.PhysicalSupportReturn
import Proof.PCP.VerifierDecodingRepeatBody

/-! A physical fixed-width record reversal. The width and record-count
sentinels are retained; each source row is copied in its original bit order. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def body : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q scan =>
    if q.val = 0 then
      some (if scan 0 then ⟨0, fun _ => none, ![.right,.left,.stay]⟩
        else ⟨1, fun _ => none, ![.left,.stay,.stay]⟩)
    else if q.val = 1 then
      some (if scan 0 then ⟨1, ![none,none,some (scan 1)], ![.left,.right,.right]⟩
        else ⟨2, fun _ => none, ![.right,.stay,.stay]⟩)
    else if q.val = 2 then
      some (if scan 0 then ⟨2, fun _ => none, ![.right,.left,.stay]⟩
        else ⟨3, fun _ => none, ![.left,.stay,.stay]⟩)
    else if q.val = 3 then
      some (if scan 0 then ⟨3, fun _ => none, ![.left,.stay,.stay]⟩
        else ⟨4, fun _ => none, ![.right,.stay,.stay]⟩)
    else none

def cfg (q : Fin 5) (B dh pos : Nat) (source out : List Bool) : Configuration 3 5 :=
  ⟨q, ![dh,pos,out.length], ![UnaryTemplate.tape B,source,out]⟩

theorem retreat_step (phase : Fin 5) (hp : phase = 0 ∨ phase = 2)
    (B i base : Nat) (hi : i < B) (source out : List Bool) :
    step body (cfg phase B (i+1) (base+(B-i)) source out) =
      some (cfg phase B (i+2) (base+(B-(i+1))) source out) := by
  rcases hp with rfl | rfl
  all_goals
    simp [step,body,cfg,Configuration.scanned,UnaryTemplate.tape_mark B i hi]
    apply configuration_ext
    · rfl
    · funext j; fin_cases j <;> simp [applyAction,HeadMove.apply] <;> omega
    · rfl

theorem retreat_stop (phase next : Fin 5) (hp : (phase = 0 ∧ next = 1) ∨ (phase = 2 ∧ next = 3))
    (B base : Nat) (source out : List Bool) :
    step body (cfg phase B (B+1) base source out) =
      some (cfg next B B base source out) := by
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp [step,body,cfg,Configuration.scanned]
    apply configuration_ext
    · rfl
    · funext j; fin_cases j <;> simp [applyAction,HeadMove.apply]
    · rfl

theorem retreat (phase next : Fin 5) (hp : (phase = 0 ∧ next = 1) ∨ (phase = 2 ∧ next = 3))
    (B n base : Nat) (hn : n ≤ B) (source out : List Bool) :
    Timed body (n+1) (cfg phase B (B-n+1) (base+n) source out)
      (cfg next B B base source out) := by
  induction n with
  | zero =>
    simpa using Timed.single (by rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl)
      (retreat_stop phase next hp B base source out)
  | succ n ih =>
    have hphase : phase=0 ∨ phase=2 := hp.imp And.left And.left
    have hs := retreat_step phase hphase B (B-(n+1)) base (by omega) source out
    have he : B-(B-(n+1))=n+1 := by omega
    have he' : B-(B-(n+1)+1)=n := by omega
    rw [he,he'] at hs
    have hindex : B-(n+1)+2=B-n+1 := by omega
    rw [hindex] at hs
    have hh := (Timed.single (by rcases hphase with rfl | rfl <;> rfl) hs).trans (ih (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem copy_step (B left : Nat) (hl : left < B) (bit : Bool) (pre tail out : List Bool) :
    step body (cfg 1 B (left+1) pre.length (pre++bit::tail) out) =
      some (cfg 1 B left (pre.length+1) (pre++bit::tail) (out++[bit])) := by
  simp [step,body,cfg,Configuration.scanned,UnaryTemplate.tape_mark B left hl,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction,HeadMove.apply]
  · funext j; fin_cases j <;> simp [applyAction,Streaming.write_append]

theorem copy_stop (B pos : Nat) (source out : List Bool) :
    step body (cfg 1 B 0 pos source out) = some (cfg 2 B 1 pos source out) := by
  simp [step,body,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem copy (B : Nat) (bits pre suffix out : List Bool) (hB : bits.length ≤ B) :
    Timed body (bits.length+1)
      (cfg 1 B bits.length pre.length (pre++bits++suffix) out)
      (cfg 2 B 1 (pre.length+bits.length) (pre++bits++suffix) (out++bits)) := by
  induction bits generalizing pre out with
  | nil => simpa using Timed.single (by rfl) (copy_stop B pre.length (pre++suffix) out)
  | cons bit bits ih =>
    have hs := Timed.single (by rfl) (copy_step B bits.length (by simp only [List.length_cons] at hB; omega) bit pre (bits++suffix) out)
    have ht := ih (pre++[bit]) (out++[bit]) (by simp only [List.length_cons] at hB; omega)
    have h := hs.trans (by simpa [List.append_assoc] using ht)
    simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem reset_step (B n : Nat) (hn : n < B) (pos : Nat) (source out : List Bool) :
    step body (cfg 3 B (n+1) pos source out)=some (cfg 3 B n pos source out) := by
  simp [step,body,cfg,Configuration.scanned,UnaryTemplate.tape_mark B n hn]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem reset_stop (B pos : Nat) (source out : List Bool) :
    step body (cfg 3 B 0 pos source out)=some (cfg 4 B 1 pos source out) := by
  simp [step,body,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem reset (B n : Nat) (hn : n ≤ B) (pos : Nat) (source out : List Bool) :
    Timed body (n+1) (cfg 3 B n pos source out) (cfg 4 B 1 pos source out) := by
  induction n with
  | zero => exact Timed.single (by rfl) (reset_stop B pos source out)
  | succ n ih =>
    have h := (Timed.single (by rfl) (reset_step B n (by omega) pos source out)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem row_run (bits pre suffix out : List Bool) :
    ∃ r, runFrom body (4*bits.length+4)
      (cfg 0 bits.length 1 (pre.length+bits.length) (pre++bits++suffix) out)=some r ∧
      r.final=cfg 4 bits.length 1 pre.length (pre++bits++suffix) (out++bits) ∧
      r.steps=4*bits.length+4 := by
  have first := retreat 0 1 (Or.inl ⟨rfl,rfl⟩) bits.length bits.length pre.length le_rfl (pre++bits++suffix) out
  have second := copy bits.length bits pre suffix out le_rfl
  have third := retreat 2 3 (Or.inr ⟨rfl,rfl⟩) bits.length bits.length pre.length le_rfl (pre++bits++suffix) (out++bits)
  have fourth := reset bits.length bits.length le_rfl pre.length (pre++bits++suffix) (out++bits)
  simp only [Nat.sub_self,Nat.zero_add] at first third
  have h := first.trans (second.trans (third.trans fourth))
  have ht : (bits.length+1)+((bits.length+1)+((bits.length+1)+(bits.length+1)))=4*bits.length+4 := by omega
  simpa only [Nat.sub_self,Nat.zero_add,ht] using h.run (by rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
