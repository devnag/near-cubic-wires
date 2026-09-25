import Proof.Packets.PhysicalMaskSerialize
/-! Reusable bank boundary for the actual monomial serializer. The source
row may lie between arbitrary resident bankPre/suffix bytes; its cursor consumes
exactly one row. Retained zero reserves are transported through the same run. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalMaskSerialize.Bank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch PhysicalMaskIndices
def cfg (bankPre support suffix : List Bool) (q : Fin 7) (index : Nat)
    (counter : List Bool) (pos : Nat) (out : List Bool) : Configuration 4 7 :=
  ⟨q, ![index+1, bankPre.length+index, pos, out.length],
    ![UnaryTemplate.tape support.length, bankPre++support++suffix, counter, out]⟩
def ready (bankPre support suffix : List Bool) (q : Fin 7) (index : Nat) (out : List Bool) : Configuration 4 7 :=
  cfg bankPre support suffix q index (UnaryTemplate.tape (index+1)) 1 out

theorem start_step (bankPre support suffix : List Bool) (out : List Bool) :
    step machine (ready bankPre support suffix 0 0 out) = some (ready bankPre support suffix 1 0 (out++[true])) := by
  simp [step,machine,ready,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem begin_step (bankPre pre rest suffix : List Bool) (bit : Bool) (out : List Bool) :
    step machine (ready bankPre (pre++bit::rest) suffix 1 pre.length out) =
      some (ready bankPre (pre++bit::rest) suffix (scanState bit) pre.length out) := by
  have hm := UnaryTemplate.tape_mark (pre++bit::rest).length pre.length (by simp)
  simp only [List.length_append,List.length_cons] at hm
  have hb := Streaming.read_append (bankPre++pre) (rest++suffix) bit
  simp only [List.length_append,List.append_assoc] at hb
  simp [step,machine,ready,cfg,Configuration.scanned,hm,List.append_assoc,hb]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem close_step (bankPre support suffix : List Bool) (out : List Bool) :
    step machine (ready bankPre support suffix 1 support.length out) =
      some (ready bankPre support suffix 6 support.length (out++[false])) := by
  simp [step,machine,ready,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem scan_step (bankPre support suffix : List Bool) (index count done : Nat)
    (selected : Bool) (out : List Bool) (h : done < count) :
    step machine (cfg bankPre support suffix (scanState selected) index (UnaryTemplate.tape count) (done+1) out) =
      some (cfg bankPre support suffix (scanState selected) index (UnaryTemplate.tape count) (done+2)
        (out++emitted selected [true])) := by
  cases selected <;>
    simp [step,machine,scanState,cfg,Configuration.scanned,UnaryTemplate.tape_mark count done h,emitted]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem delimiter_step (bankPre support suffix : List Bool) (index count : Nat)
    (selected : Bool) (out : List Bool) :
    step machine (cfg bankPre support suffix (scanState selected) index (UnaryTemplate.tape count) (count+1) out) =
      some (cfg bankPre support suffix 4 index (grown count) (count+2)
        (out++emitted selected [false])) := by
  cases selected <;> simp [step,machine,scanState,cfg,Configuration.scanned,emitted]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append,grow_end]

theorem sentinel_step (bankPre support suffix : List Bool) (index count : Nat) (out : List Bool) :
    step machine (cfg bankPre support suffix 4 index (grown count) (count+2) out) =
      some (cfg bankPre support suffix 5 index (UnaryTemplate.tape (count+1)) (count+1) out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]
    have hh := Streaming.write_append (grown count) false
    simpa [grown,UnaryTemplate.tape] using hh

theorem back_step (bankPre support suffix : List Bool) (index count pos : Nat) (out : List Bool)
    (h : pos < count) :
    step machine (cfg bankPre support suffix 5 index (UnaryTemplate.tape count) (pos+1) out) =
      some (cfg bankPre support suffix 5 index (UnaryTemplate.tape count) pos out) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark count pos h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem advance_step (bankPre support suffix : List Bool) (index count : Nat) (out : List Bool) :
    step machine (cfg bankPre support suffix 5 index (UnaryTemplate.tape count) 0 out) =
      some (cfg bankPre support suffix 1 (index+1) (UnaryTemplate.tape count) 1 out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · rfl

theorem scan_prefix (bankPre support suffix : List Bool) (index remaining done : Nat)
    (selected : Bool) (out : List Bool) :
    Timed machine (remaining+1)
      (cfg bankPre support suffix (scanState selected) index (UnaryTemplate.tape (done+remaining)) (done+1) out)
      (cfg bankPre support suffix 4 index (grown (done+remaining)) (done+remaining+2)
        (out++emitted selected (List.replicate remaining true++[false]))) := by
  induction remaining generalizing done out with
  | zero =>
    have hh : machine.halted (scanState selected) = false := by cases selected <;> rfl
    simpa using Timed.single hh (delimiter_step bankPre support suffix index done selected out)
  | succ remaining ih =>
    have hh : machine.halted (scanState selected) = false := by cases selected <;> rfl
    have first := Timed.single hh
      (scan_step bankPre support suffix index (done+(remaining+1)) done selected out (by omega))
    have tail := ih (done+1) (out++emitted selected [true])
    have h := first.trans (by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail)
    cases selected <;>
      simpa [emitted,List.replicate_succ,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem return_prefix (bankPre support suffix : List Bool) (index count pos : Nat)
    (out : List Bool) (h : pos ≤ count) :
    Timed machine (pos+1)
      (cfg bankPre support suffix 5 index (UnaryTemplate.tape count) pos out)
      (cfg bankPre support suffix 1 (index+1) (UnaryTemplate.tape count) 1 out) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (advance_step bankPre support suffix index count out)
  | succ pos ih =>
    exact Timed.step (by rfl) (back_step bankPre support suffix index count pos out (by omega)) (ih (by omega))

theorem branch_prefix (bankPre support suffix : List Bool) (index : Nat) (selected : Bool) (out : List Bool) :
    Timed machine (2*index+6) (ready bankPre support suffix (scanState selected) index out)
      (ready bankPre support suffix 1 (index+1) (out++emitted selected (ExtIncidence.block index))) := by
  have first := scan_prefix bankPre support suffix index (index+1) 0 selected out
  simp only [Nat.zero_add] at first
  have next := Timed.single (by rfl) (sentinel_step bankPre support suffix index (index+1)
    (out++emitted selected (List.replicate (index+1) true++[false])))
  have last := return_prefix bankPre support suffix index (index+1+1) (index+1+1)
    (out++emitted selected (List.replicate (index+1) true++[false])) le_rfl
  have h := (first.trans next).trans last
  have ht : index+1+1+1+(index+1+1+1)=2*index+6 := by omega
  rw [ht] at h
  simpa only [ready,ExtIncidence.block] using h

theorem loop_prefix (bankPre pre rest suffix : List Bool) (out : List Bool) :
    Timed machine (rest.length*(2*pre.length+rest.length+6)+1)
      (ready bankPre (pre++rest) suffix 1 pre.length out)
      (ready bankPre (pre++rest) suffix 6 (pre++rest).length
        (out++(selectedIndices pre.length rest).flatMap ExtIncidence.block++[false])) := by
  induction rest generalizing pre out with
  | nil => simpa [selectedIndices] using Timed.single (by rfl) (close_step bankPre pre suffix out)
  | cons bit rest ih =>
    have first := Timed.single (by rfl) (begin_step bankPre pre rest suffix bit out)
    have branch := branch_prefix bankPre (pre++bit::rest) suffix pre.length bit out
    have tail := ih (pre++[bit]) (out++emitted bit (ExtIncidence.block pre.length))
    have h := (first.trans branch).trans (by
      simpa [List.append_assoc] using tail)
    have time : 1+(2*pre.length+6)+(rest.length*(2*(pre.length+1)+rest.length+6)+1)=
        (rest.length+1)*(2*pre.length+(rest.length+1)+6)+1 := by ring
    rw [time] at h
    cases bit <;> simpa [selectedIndices,emitted,List.append_assoc] using h

/-- Complete mask-to-native-word execution, including start/end marks and all
physical unary-counter growth and return scans. -/
theorem monomial_run (bankPre support suffix : List Bool) (out : List Bool) :
    ∃ r, runFrom machine (support.length^2+6*support.length+2)
      (ready bankPre support suffix 0 0 out)=some r ∧
      r.final=ready bankPre support suffix 6 support.length
        (out++ExtIncidence.monomialWord (selectedIndices 0 support)) ∧
      r.steps=support.length^2+6*support.length+2 := by
  have first := Timed.single (by rfl) (start_step bankPre support suffix out)
  have tail := loop_prefix bankPre [] support suffix (out++[true])
  simp only [List.nil_append,List.length_nil,Nat.mul_zero,Nat.zero_add] at tail
  have h := first.trans tail
  have ht : 1+(support.length*(support.length+6)+1)=support.length^2+6*support.length+2 := by ring
  rw [ht] at h
  simpa [ExtIncidence.monomialWord,List.append_assoc] using h.run (by rfl)


/-- Existing retained zero cells remain allocated and are charged by the
original receipt transport; the program and its paid time are unchanged. -/
theorem padded_run (bankPre support suffix out : List Bool) (capacity : Fin 4 → Nat) :
    ∃ r, runFrom machine (support.length^2+6*support.length+2)
      (ZeroPadding.config capacity (ready bankPre support suffix 0 0 out))=some r ∧
      r.final=ZeroPadding.config capacity
        (ready bankPre support suffix 6 support.length
          (out++ExtIncidence.monomialWord (selectedIndices 0 support))) ∧
      r.steps=support.length^2+6*support.length+2 := by
  obtain ⟨base,hb,hf,hs⟩ := monomial_run bankPre support suffix out
  obtain ⟨r,hr,hrf,hrs,_⟩ := ZeroPadding.run_config machine capacity _ _ base hb
  exact ⟨r,hr,by simpa [hf] using hrf,hrs.trans hs⟩

end PCJ9eff70d512234a4c_Fixed.PhysicalMaskSerialize.Bank
