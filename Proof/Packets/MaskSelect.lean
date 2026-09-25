import Proof.Packets.ParityCandidateSuffix

/-! Physical conditional decoding of one framed support record. The decision
is read from the coefficient tape; each retained row increments a real unary
counter, while a rejected row emits no mask bits. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskSelect
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

@[simp] theorem read_flag (b : Bool) : readTapeBit [b] 0 = b := rfl

def machine : Machine 4 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==5
  rule := fun q scan =>
    if q.val=0 then
      some ⟨if scan 0 then 1 else 2,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=1 then
      some ⟨0,![none,if scan 3 then some (scan 0) else none,none,none],
        ![.right,if scan 3 then .right else .stay,.stay,.stay]⟩
    else if q.val=2 then some ⟨3,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=3 then some ⟨4,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=4 then
      some ⟨5,![none,none,if scan 3 then some true else none,none],
        ![.stay,.stay,if scan 3 then .right else .stay,.stay]⟩
    else none

def cfg (q : Fin 6) (source : List Bool) (pos : Nat) (out : List Bool) (kept : Nat) (keep : Bool) :
    Configuration 4 6 :=
  ⟨q,![pos,out.length,kept+1,0],![source,out,CompareMachine.word kept,[keep]]⟩

def output (keep : Bool) (bits : List Bool) := if keep then bits else []

theorem marker_step (pre tail out : List Bool) (kept : Nat) (keep : Bool) :
    step machine (cfg 0 (pre++true::tail) pre.length out kept keep)=
      some (cfg 1 (pre++true::tail) (pre.length+1) out kept keep) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem bit_step (bit : Bool) (pre tail out : List Bool) (kept : Nat) (keep : Bool) :
    step machine (cfg 1 (pre++bit::tail) pre.length out kept keep)=
      some (cfg 0 (pre++bit::tail) (pre.length+1) (out++output keep [bit]) kept keep) := by
  cases keep <;> simp [step,machine,cfg,output,Configuration.scanned,Streaming.read_append]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,Streaming.write_append]

theorem terminal_step (pre suffix out : List Bool) (kept : Nat) (keep : Bool) :
    step machine (cfg 0 (pre++false::suffix) pre.length out kept keep)=
      some (cfg 2 (pre++false::suffix) (pre.length+1) out kept keep) := by
  simp [step,machine,cfg,Configuration.scanned,Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem skip_first (source out : List Bool) (pos kept : Nat) (keep : Bool) :
    step machine (cfg 2 source pos out kept keep)=some (cfg 3 source (pos+1) out kept keep) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem skip_second (source out : List Bool) (pos kept : Nat) (keep : Bool) :
    step machine (cfg 3 source pos out kept keep)=some (cfg 4 source (pos+1) out kept keep) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem bump_step (source out : List Bool) (pos kept : Nat) (keep : Bool) :
    step machine (cfg 4 source pos out kept keep)=some (cfg 5 source pos out (kept+keep.toNat) keep) := by
  have hw : writeTapeBit (CompareMachine.word kept) (kept+1) true=CompareMachine.word (kept+1) := by
    simpa [CompareMachine.word,List.replicate_add] using Streaming.write_append (CompareMachine.word kept) true
  cases keep <;> simp [step,machine,cfg,Configuration.scanned]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
    · funext i; fin_cases i <;> simp [applyAction,hw]

theorem field_prefix (bits pre suffix out : List Bool) (kept : Nat) (keep : Bool) :
    Timed machine (2*bits.length+1)
      (cfg 0 (pre++frame bits++suffix) pre.length out kept keep)
      (cfg 2 (pre++frame bits++suffix) (pre.length+(frame bits).length)
        (out++output keep bits) kept keep) := by
  induction bits generalizing pre out with
  | nil => simpa [frame,output] using Timed.single (by rfl) (terminal_step pre suffix out kept keep)
  | cons bit bits ih =>
    have first := Timed.single (by rfl) (marker_step pre (bit::(frame bits++suffix)) out kept keep)
    have second := Timed.single (by rfl) (bit_step bit (pre++[true]) (frame bits++suffix) out kept keep)
    have second' : Timed machine 1
      (cfg 1 (pre++true::bit::(frame bits++suffix)) (pre.length+1) out kept keep)
      (cfg 0 (pre++true::bit::(frame bits++suffix)) (pre.length+2)
        (out++output keep [bit]) kept keep) := by
      simpa [List.append_assoc] using second
    have rest := ih (pre++[true,bit]) (out++output keep [bit])
    have h := first.trans (second'.trans (by simpa [List.append_assoc] using rest))
    have hout : output keep [bit]++output keep bits=output keep (bit::bits) := by cases keep <;> rfl
    have ht : 1+(1+(2*bits.length+1))=2*(bits.length+1)+1 := by omega
    rw [ht] at h
    have hpos : pre.length+2+(2*bits.length+1)=pre.length+(frame (bit::bits)).length := by
      simp only [List.length_cons,frame_length]
      omega
    rw [hpos] at h
    simpa only [frame,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append,
      List.length_cons,hout] using h

/-- The coefficient flag controls both emitted support bytes and the exact
kept-row counter; every input field byte is consumed by a real transition. -/
theorem select_run (bits pre suffix out : List Bool) (kept : Nat) (keep : Bool) :
    ∃ r,runFrom machine (2*bits.length+4)
      (cfg 0 (pre++frame bits++[false,false]++suffix) pre.length out kept keep)=some r ∧
      r.final=cfg 5 (pre++frame bits++[false,false]++suffix)
        (pre.length+(frame bits).length+2) (out++output keep bits) (kept+keep.toNat) keep ∧
      r.steps=2*bits.length+4 := by
  have first := field_prefix bits pre ([false,false]++suffix) out kept keep
  have second := Timed.single (by rfl) (skip_first (pre++frame bits++[false,false]++suffix)
    (out++output keep bits) (pre.length+(frame bits).length) kept keep)
  have third := Timed.single (by rfl) (skip_second (pre++frame bits++[false,false]++suffix)
    (out++output keep bits) (pre.length+(frame bits).length+1) kept keep)
  have fourth := Timed.single (by rfl) (bump_step (pre++frame bits++[false,false]++suffix)
    (out++output keep bits) (pre.length+(frame bits).length+2) kept keep)
  have tail := second.trans (third.trans fourth)
  have h := first.trans (by simpa only [List.append_assoc] using tail)
  have time : 2*bits.length+1+(1+(1+1))=2*bits.length+4 := by omega
  simpa only [time,List.append_assoc] using h.run (by rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskSelect
